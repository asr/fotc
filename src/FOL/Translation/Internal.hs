------------------------------------------------------------------------------
-- Translation of Agda internal syntax entities to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Internal
  ( cBodyToFormula
  , cBodyToFOLTerm
  , removeBindingOnCBody
  ) where

-- Haskell imports
-- import Control.Monad.Trans.Reader ( ask, local )
-- import Control.Monad.Trans.State ( evalState )

-- Agda library imports
import Agda.Syntax.Common ( Nat )
import Agda.Syntax.Internal
  ( Abs(Abs)
  , ClauseBody(Bind,Body)
--  , Telescope(EmptyTel, ExtendTel)
  )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

-- Local imports
import AgdaLib.Syntax.DeBruijn        ( renameVar, varToDeBruijnIndex )
import AgdaLib.EtaExpansion           ( etaExpand )
import FOL.Translation.Internal.Terms ( termToFormula, termToFOLTerm )
import FOL.Types                      ( FOLFormula, FOLTerm )
import Monad.Base                     ( T )
import Monad.Reports                  ( reportSLn )

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

cBodyToFormula ∷ ClauseBody → T FOLFormula
cBodyToFormula (Body term)          = etaExpand term >>= termToFormula
cBodyToFormula (Bind (Abs _ cBody)) = cBodyToFormula cBody
cBodyToFormula _                    = __IMPOSSIBLE__

cBodyToFOLTerm ∷ ClauseBody → T FOLTerm
-- We don't eta-expand the term before the translation, because we
-- cannot translate the lambda abstractions generated to FOL terms.
cBodyToFOLTerm (Body term)          = termToFOLTerm term
cBodyToFOLTerm (Bind (Abs _ cBody)) = cBodyToFOLTerm cBody
cBodyToFOLTerm _                    = __IMPOSSIBLE__

removeBindingOnCBodyIndex ∷ ClauseBody → String → Nat → ClauseBody
removeBindingOnCBodyIndex (Bind (Abs x1 cBody)) x2 index =
  if x1 == x2
    then renameVar cBody index  -- We remove the bind and rename the
                                -- variables inside the body.
  else Bind (Abs x1 $ removeBindingOnCBodyIndex cBody x2 index)
removeBindingOnCBodyIndex _ _ _ = __IMPOSSIBLE__

-- To remove the binding on a proof term in a ClauseBody,
--
-- e.g. remove the binding on Nn : N n where D : Set, n : D and N : D → Set.
--
-- We know that the bounded variable is a proof term from the
-- invocation to this function.
removeBindingOnCBody ∷ ClauseBody → String → T ClauseBody
removeBindingOnCBody cBody x = do
  let index ∷ Nat
      index = varToDeBruijnIndex cBody x

  reportSLn "remove" 20 $ "The index is: " ++ show index

  return $ removeBindingOnCBodyIndex cBody x index
