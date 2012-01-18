------------------------------------------------------------------------------
-- |
-- Module      : FOL.Translation.Internal
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Translation of Agda internal syntax entities to FOL formulas.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Internal
  ( cBodyToFormula
  , cBodyToFOLTerm
  , dropBindingOnCBody
  ) where

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Common ( Nat )

import Agda.Syntax.Internal
  ( Abs(Abs)
  , ClauseBody(Bind,Body)
  )

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import AgdaLib.DeBruijn      ( ChangeIndex(changeIndex), varToIndex )
import AgdaLib.EtaExpansion  ( EtaExpandible(etaExpand) )
import FOL.Translation.Terms ( termToFormula, termToFOLTerm )
import FOL.Types             ( FOLFormula, FOLTerm )
import Monad.Base            ( T )
import Monad.Reports         ( reportSLn )

#include "../../undefined.h"

------------------------------------------------------------------------------
-- A ClauseBody is defined by (Agda.Syntax.Internal)
-- data ClauseBody = Body Term
-- 		| Bind (Abs ClauseBody)
-- 		| NoBind ClauseBody
-- 		| NoBody    -- for absurd clauses

-- telescopeToFormula ∷ Telescope → T FOLFormula
-- telescopeToFormula EmptyTel             = __IMPOSSIBLE__
-- telescopeToFormula (ExtendTel tyArg _) = typeToFormula $ unArg tyArg

-- | Translate an Agda internal ClauseBody to an FOL formula.
cBodyToFormula ∷ ClauseBody → T FOLFormula
cBodyToFormula (Body term)          = etaExpand term >>= termToFormula
cBodyToFormula (Bind (Abs _ cBody)) = cBodyToFormula cBody
cBodyToFormula _                    = __IMPOSSIBLE__

-- | Translate an Agda internal ClauseBody to an FOL term.
cBodyToFOLTerm ∷ ClauseBody → T FOLTerm
-- We don't eta-expand the term before the translation, because we
-- cannot translate the generated lambda abstractions to FOL terms.
cBodyToFOLTerm (Body term)          = termToFOLTerm term
cBodyToFOLTerm (Bind (Abs _ cBody)) = cBodyToFOLTerm cBody
cBodyToFOLTerm _                    = __IMPOSSIBLE__

dropBindingOnCBodyIndex ∷ ClauseBody → String → Nat → ClauseBody
dropBindingOnCBodyIndex (Bind (Abs x1 cBody)) x2 index =
  if x1 == x2
    then changeIndex cBody index  -- We drop the bind and rename the
                                  -- variables inside the body.
    else Bind (Abs x1 $ dropBindingOnCBodyIndex cBody x2 index)
dropBindingOnCBodyIndex _ _ _ = __IMPOSSIBLE__

-- To drop the binding on a proof term in a ClauseBody,
--
-- e.g. drop the binding on Nn : N n where D : Set, n : D and N : D → Set.
--
-- We know that the bounded variable is a proof term from the
-- invocation to this function.
dropBindingOnCBody ∷ ClauseBody → String → T ClauseBody
dropBindingOnCBody cBody x = do
  let index ∷ Nat
      index = varToIndex cBody x

  reportSLn "drop" 20 $ "The index is: " ++ show index

  return $ dropBindingOnCBodyIndex cBody x index
