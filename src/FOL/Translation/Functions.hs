------------------------------------------------------------------------------
-- |
-- Module      : FOL.Translation.Functions
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Translation of Agda internal functions to fisrt-order logic
-- formulae.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

-- Only are translated the functions that will be translate as TPTP
-- definitions.

module FOL.Translation.Functions ( fnToFormula ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad       ( liftM2, replicateM, replicateM_, when )
import Control.Monad.Error ( MonadError(throwError) )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common
  ( Arg(Arg)
  , Dom(Dom)
  , Hiding(NotHidden)
  , Nat
  , Relevance(Relevant)
  )

import Agda.Syntax.Abstract.Name ( QName )

import Agda.Syntax.Internal
  ( Abs(Abs)
  , Clause(Clause)
  , ClauseBody
  , Level(Max)
  , PlusLevel(ClosedLevel)
  , Sort(Type)
  , Tele(ExtendTel)
  , Telescope
  , Term(Def)
  , Type(El)
  , var
  )

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import AgdaInternal.DeBruijn ( DecIndex(decIndex) )
import AgdaInternal.Vars     (BoundedVars(boundedVars))
import FOL.Primitives        ( equal )

import FOL.Translation.ClauseBody
  ( cBodyToFormula
  , cBodyToFOLTerm
  , dropProofTermOnCBody
  )

import FOL.Translation.Terms ( termToFormula, termToFOLTerm )
import FOL.Translation.Types ( typeToFormula )
import FOL.Types             ( FOLFormula(Implies, Equiv, ForAll) )

import Monad.Base
  ( getTVars
  , popTVar
  , pushTNewVar
  , T
  )

import Monad.Reports ( reportSLn )

#include "../../undefined.h"

------------------------------------------------------------------------------
-- Auxiliary functions

varsToArgs ∷ Nat → [Arg Term]
varsToArgs 0 = []
varsToArgs n = Arg NotHidden Relevant (var (n - 1)) : varsToArgs (n - 1)

------------------------------------------------------------------------------
-- In general a definition's function is given by various clauses
-- (i.e. equations), for example every equation in a definition by
-- pattern matching. In our case it is only necessary to translate
-- definitions with only one clause.

-- | Translate an ATP definition to a first-order logic formula
-- 'FOLFormula'.
fnToFormula ∷ QName → Type → [Clause] → T FOLFormula
fnToFormula _      _  []        = __IMPOSSIBLE__
fnToFormula qName  ty (cl : []) = clauseToFormula qName ty cl
fnToFormula qName  _  _         =
  throwError $ "The translation of " ++ show qName
               ++ " failed because its definition only can have a clause"

-- A Clause is defined by (Agda.Syntax.Internal)
-- data Clause = Clause
--     { clauseRange     ∷ Range
--     , clauseTel       ∷ Telescope
--     , clausePerm      ∷ Permutation
--     , clausePats      ∷ [Arg Pattern]
--     , clauseBody      ∷ ClauseBody
--     }

-- The LHS of the definition's function is given by the @QName@ and
-- the @Type@. The RHS is given by the @Clause@. Before translate the
-- LHS and the RHS (i.e. the body of the clause) it is necessary to
-- generate an universal quantification on an equal number of
-- variables to length @[Arg Pattern]@.
clauseToFormula ∷ QName → Type → Clause → T FOLFormula

-- There is at most one variable in the clause's pattern.
clauseToFormula qName ty (Clause r tel perm (_ : pats) cBody) =
  case tel of
    -- The bounded variable is quantified on a @Set@,
    --
    -- e.g. the bounded variable is @d : D@ where @D : Set@,
    --
    -- so we can create a fresh variable and quantify on it without any
    -- problem.
    --
    -- N.B. the pattern matching on @(Def _ [])@.
    ExtendTel (Dom _ _ (El (Type (Max [])) (Def _ []))) (Abs x tels) → do
      reportSLn "def2f" 20 $ "Processing variable " ++ show x

      freshVar ← pushTNewVar
      -- We process forward in the telescope and the pattern.
      f ← clauseToFormula qName ty (Clause r tels perm pats cBody)
      popTVar

      return $ ForAll freshVar (\_ → f)

    -- The bounded variable is quantified on a proof,
    --
    -- e.g. the bounded variable is @Nn : N n@ where @D : Set@, @n :
    -- D@, and @N : D → Set@,
    --
    -- so we need drop this quantification. In this case, we erase the
    -- quantification on the bounded variable and we try it as a
    -- function type (using @Implies@ instead of @ForAll@).

    -- N.B. the pattern matching on @(Def _ _)@.
    ExtendTel (Dom _ _ tye@(El (Type (Max [])) (Def _ _))) (Abs x tels) → do
      reportSLn "def2f" 20 $ "Processing proof term " ++ show x

      reportSLn "def2f" 20 $ "tye: " ++ show tye

      f1 ← typeToFormula tye

      reportSLn "def2f" 20 $ "f1: " ++ show f1

      reportSLn "def2f" 20 $ "Current body: " ++ show cBody

      newBody ∷ ClauseBody ← dropProofTermOnCBody cBody x

      -- Just to force the evaluation of @newBody@.
      when (null $ show newBody) (__IMPOSSIBLE__)

      reportSLn "def2f" 20 $ "New body: " ++ show newBody

      let decTels ∷ Telescope
          decTels = decIndex tels

      reportSLn "def2f" 20 $ "tels: " ++ show tels
      reportSLn "def2f" 20 $ "decTels: " ++ show decTels

      -- We process forward in the telescope and the pattern.
      f2 ← clauseToFormula qName ty (Clause r decTels perm pats newBody)

      reportSLn "def2f" 20 $ "f2: " ++ show f2

      return $ Implies f1 f2

    _ → __IMPOSSIBLE__

-- The clause's patterns is empty, i.e. we have generated the required
-- universal quantification, so we translate the LHS and the RHS.
clauseToFormula qName ty (Clause _ _ _ [] cBody) = do
  vars ← getTVars
  reportSLn "def2f" 20 $ "vars: " ++ show vars

  case ty of
    -- The defined symbol is a predicate.
    El (Type (Max [ClosedLevel 1])) _ → do

      -- We create the Agda term corresponds to the LHS of the symbol's
      -- definition.
      let lhs ∷ Term
          lhs = Def qName $ varsToArgs $ fromIntegral $ length vars

      -- Because the LHS and the RHS (the body of the clause) are
      -- formulae, they are related via an equivalence logic.
      liftM2 Equiv (termToFormula lhs) (cBodyToFormula cBody)

    -- The defined symbol is a function.
    El (Type (Max [])) _ → do
      let totalBoundedVars ∷ Int
          totalBoundedVars = boundedVars cBody

      -- We create the Agda term corresponds to the LHS of the symbol's
      -- definition.

      -- We use @totalBoundedVars@ because we need to handle definitions like
      --
      -- @foo ∷ D → D@
      -- @foo = λ d → ...

      let lhs ∷ Term
          lhs = Def qName $ varsToArgs $ fromIntegral totalBoundedVars

      if length vars == totalBoundedVars
        -- The definition is of the form
        --
        -- @foo ∷ D → D@
        -- @foo d = ...
        --
        -- so we don't need to add new fresh variables.
        then liftM2 equal (termToFOLTerm lhs) (cBodyToFOLTerm cBody)
        -- The definition is of the form
        --
        -- @foo ∷ D → D@
        -- @foo = λ d → ...
        --
        -- so we need to add some fresh variables to the state before
        -- call the translation for @lhs@ and @cBody@.
        else if length vars < totalBoundedVars
          then do
            let diff ∷ Int
                diff = totalBoundedVars - length vars

            freshVars ← replicateM diff pushTNewVar
            reportSLn "def2f" 20 $ "Freshvars: " ++ show freshVars
            tLHS ← termToFOLTerm lhs
            replicateM_ diff popTVar
            tRHS ← cBodyToFOLTerm cBody

            -- Because the LHS and the RHS (the body of the clause) are
            -- terms, they are related via the first-order logic equaliy.
            let helper ∷ [String] → FOLFormula
                helper []       = __IMPOSSIBLE__
                helper (x : []) = ForAll x $ \_ → equal tLHS tRHS
                helper (x : xs) = ForAll x $ \_ → helper xs

            return $ helper freshVars
          else __IMPOSSIBLE__

    _ → __IMPOSSIBLE__
