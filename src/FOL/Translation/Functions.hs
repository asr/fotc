------------------------------------------------------------------------------
-- |
-- Module      : FOL.Translation.Functions
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Translation of Agda internal functions to FOL formulas.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

-- Only are translated the functions that will be translate as TPTP
-- definitions.

module FOL.Translation.Functions ( fnToFormula ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad       ( liftM2, when )
import Control.Monad.Error ( MonadError(throwError) )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common        ( Arg(Arg) )
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
  )

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import AgdaLib.DeBruijn       ( DecIndex(decIndex) )
import FOL.Primitives         ( equal )
import FOL.Translation.Common ( varsToArgs )

import FOL.Translation.Internal
  ( cBodyToFormula
  , cBodyToFOLTerm
  , dropBindingOnCBody
  )

import FOL.Translation.Terms ( termToFormula, termToFOLTerm )
import FOL.Translation.Types ( typeToFormula )
import FOL.Types             ( FOLFormula(Implies, Equiv, ForAll) )

import Monad.Base
  ( getTVars
  , newTVar
  , popTVar
  , pushTVar
  , T
  )

import Monad.Reports ( reportSLn )

#include "../../undefined.h"

------------------------------------------------------------------------------
-- In general a definition's function is given by various clauses
-- (i.e. equations), for example every equation in a definition by
-- pattern matching. In our case it is only necessary to translate
-- definitions with only one clause.

-- | Translate an ATP definition to an FOL formula.
fnToFormula ∷ QName → Type → [Clause] → T FOLFormula
fnToFormula _      _  []        = __IMPOSSIBLE__
fnToFormula qName  ty (cl : []) = clauseToFormula qName ty cl
fnToFormula _      _  _         =
  throwError "The definitions to be translate only can have a clause"

-- A Clause is defined by (Agda.Syntax.Internal)
-- data Clause = Clause
--     { clauseRange     ∷ Range
--     , clauseTel       ∷ Telescope
--     , clausePerm      ∷ Permutation
--     , clausePats      ∷ [Arg Pattern]
--     , clauseBody      ∷ ClauseBody
--     }

-- The LHS of the definition's function is given by the QName and the
-- Type. The RHS is given by the Clause. Before translate the LHS and
-- the RHS (i.e. the body of the clause) it is necessary to generate
-- an universal quantification on an equal number of variables to
-- length [Arg Pattern].
clauseToFormula ∷ QName → Type → Clause → T FOLFormula

-- There is at most one variable in the clause's pattern.
clauseToFormula qName ty (Clause r tel perm (_ : pats) cBody) =
  case tel of
    -- The bounded variable is quantified on a Set,
    --
    -- e.g. the bounded variable is 'd : D' where D : Set,
    --
    -- so we can create a fresh variable and quantify on it without any
    -- problem. N.B. the pattern matching on (Def _ []).
    ExtendTel (Arg _ _ (El (Type (Max [])) (Def _ []))) (Abs x tels) → do
      reportSLn "def2f" 20 $ "Processing variable: " ++ x

      freshVar ← newTVar
      pushTVar freshVar
      -- We process forward in the telescope and the pattern.
      f ← clauseToFormula qName ty (Clause r tels perm pats cBody)
      popTVar

      return $ ForAll freshVar (\_ → f)

    -- The bounded variable is quantified on a proof,
    --
    -- e.g. the bounded variable is 'Nn : N n' where D : Set, n : D,
    -- and N : D → Set,
    --
    -- so we need drop this quantification. In this case, we erase the
    -- quantification on the bounded variable and we try it as a
    -- function type (using Implies instead of ForAll).

    -- N.B. the pattern matching on (Def _ _).
    ExtendTel (Arg _ _ tye@(El (Type (Max [])) (Def _ _))) (Abs x tels) → do
      reportSLn "def2f" 20 $ "Processing proof term: " ++ x

      reportSLn "def2f" 20 $ "tye: " ++ show tye

      f1 ← typeToFormula tye

      reportSLn "def2f" 20 $ "f1: " ++ show f1

      reportSLn "def2f" 20 $ "Current body: " ++ show cBody

      newBody ∷ ClauseBody ← dropBindingOnCBody cBody x

      -- Just to force the evaluation of newBody.
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

  -- We create the Agda term corresponds to the LHS of the symbol's
  -- definition.
  let lhs ∷ Term
      lhs = Def qName $ varsToArgs $ fromIntegral $ length vars

  case ty of
    -- The defined symbol is a predicate.
    El (Type (Max [ClosedLevel 1])) _ →
       -- Because the LHS and the RHS (the body of the clause) are
       -- formulas, they are related via an equivalence logic.
       liftM2 Equiv (termToFormula lhs) (cBodyToFormula cBody)

    -- The defined symbol is a function.
    El (Type (Max [])) _ →
       -- Because the LHS and the RHS (the body of the clause) are
       -- terms, they are related via the FOL equaliy
       liftM2 equal (termToFOLTerm lhs) (cBodyToFOLTerm cBody)

    _ → __IMPOSSIBLE__
