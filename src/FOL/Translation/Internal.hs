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
--    , Telescope(EmptyTel, ExtendTel)
    )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

-- Local imports
import FOL.Monad ( T )
import FOL.Translation.Internal.Terms ( termToFormula, termToFOLTerm )
-- import FOL.Translation.Internal.Types ( typeToFormula )
import FOL.Types ( FOLFormula, FOLTerm )
import MyAgda.Syntax.DeBruijn ( renameVar, varToDeBruijnIndex )

#include "../../undefined.h"

------------------------------------------------------------------------------
-- A ClauseBody is defined by (Agda.Syntax.Internal)
-- data ClauseBody = Body Term
-- 		| Bind (Abs ClauseBody)
-- 		| NoBind ClauseBody
-- 		| NoBody    -- for absurd clauses

-- telescopeToFormula :: Telescope → T FOLFormula
-- telescopeToFormula EmptyTel             = __IMPOSSIBLE__
-- telescopeToFormula (ExtendTel tyArg _ ) = typeToFormula $ unArg tyArg

cBodyToFormula :: ClauseBody → T FOLFormula
cBodyToFormula (Body term )         = termToFormula term
cBodyToFormula (Bind (Abs _ cBody)) = cBodyToFormula cBody
cBodyToFormula _                    = __IMPOSSIBLE__

cBodyToFOLTerm :: ClauseBody → T FOLTerm
cBodyToFOLTerm (Body term )         = termToFOLTerm term
cBodyToFOLTerm (Bind (Abs _ cBody)) = cBodyToFOLTerm cBody
cBodyToFOLTerm _                    = __IMPOSSIBLE__

removeBindingOnCBodyIndex :: ClauseBody → String → Nat → ClauseBody
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
removeBindingOnCBody :: ClauseBody → String → ClauseBody
removeBindingOnCBody cBody x = removeBindingOnCBodyIndex cBody x index
    where
      index :: Nat
      index = varToDeBruijnIndex cBody x
