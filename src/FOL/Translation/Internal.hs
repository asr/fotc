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
import MyAgda.Syntax.Internal ( renameVar )

#include "../../undefined.h"

------------------------------------------------------------------------------

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

posVarOnCBody :: ClauseBody → String → Nat
posVarOnCBody (Bind (Abs x1 cBody)) x2
    | x1 == x2 = 0
    | otherwise    = 1 + posVarOnCBody cBody x2
-- In other cases it hasn't sense. In addition, we must find the
-- variable before reach the Body.
posVarOnCBody _ _ = __IMPOSSIBLE__

-- To remove the binding on a proof term in a ClauseBody,
--
-- e.g. remove the binding on Nn : N n where D : Set, n : D and N : D → Set.
--
-- We know that the bounded variable is a proof term from the
-- invocation to this function.
removeBindingOnCBodyPos :: ClauseBody → String → Nat → ClauseBody
removeBindingOnCBodyPos (Bind (Abs x1 cBody)) x2 pos =
    if x1 == x2
       then renameVar cBody pos -- We remove the bind and rename the
                                -- variables inside the body.
       else (Bind (Abs x1 $ removeBindingOnCBodyPos cBody x2 pos))
removeBindingOnCBodyPos _ _ _ = __IMPOSSIBLE__

removeBindingOnCBody :: ClauseBody → String → ClauseBody
removeBindingOnCBody cBody x = removeBindingOnCBodyPos cBody x pos
    where
    pos :: Nat
    pos = posVarOnCBody cBody x
