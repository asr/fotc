------------------------------------------------------------------------------
-- Translation of Agda internal syntax entities to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module FOL.Translation.Internal.Internal
    ( cBodyToFormula
    , cBodyToTermFOL
    , removeBindingOnCBody
    ) where

-- Haskell imports
-- import Control.Monad.Trans.Reader ( ask, local )
-- import Control.Monad.Trans.State ( evalState )

-- Agda library imports
import Agda.Syntax.Common
    ( Arg(Arg)
    , Nat
--    , unArg
    )
import Agda.Syntax.Internal
    ( Abs(Abs)
    , ClauseBody(Bind,Body)
--    , Telescope(EmptyTel, ExtendTel)
    , Term(Def, Var)
    )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

-- Local imports
import FOL.Monad ( T )
import FOL.Translation.Internal.Terms ( termToFormula, termToTermFOL )
-- import FOL.Translation.Internal.Types ( typeToFormula )
import FOL.Types ( FormulaFOL, TermFOL )

#include "../../../undefined.h"

------------------------------------------------------------------------------

-- telescopeToFormula :: Telescope -> T FormulaFOL
-- telescopeToFormula EmptyTel             = __IMPOSSIBLE__
-- telescopeToFormula (ExtendTel tyArg _ ) = typeToFormula $ unArg tyArg

cBodyToFormula :: ClauseBody -> T FormulaFOL
cBodyToFormula (Body term )         = termToFormula term
cBodyToFormula (Bind (Abs _ cBody)) = cBodyToFormula cBody
cBodyToFormula _                    = __IMPOSSIBLE__

cBodyToTermFOL :: ClauseBody -> T TermFOL
cBodyToTermFOL (Body term )         = termToTermFOL term
cBodyToTermFOL (Bind (Abs _ cBody)) = cBodyToTermFOL cBody
cBodyToTermFOL _                    = __IMPOSSIBLE__

posVarOnCBody :: ClauseBody -> String -> Nat
posVarOnCBody (Bind (Abs var1 cBody)) var2
    | var1 == var2 = 0
    | otherwise    = 1 + posVarOnCBody cBody var2
-- In other cases it hasn't sense. In addition, we must find the
-- variable before reach the Body.
posVarOnCBody _ _ = __IMPOSSIBLE__

renameVarOnArgVar :: Arg Term -> Nat -> Arg Term
renameVarOnArgVar var@(Arg h (Var n [])) pos
    | n < pos = var -- The variable was before than the quantified
                    -- variable, we don't do nothing.
    | n > pos = Arg h (Var (n - 1) []) -- The variable was after
                                       -- than the quantified
                                       -- variable, we need
                                       -- "unbound" the quantified
                                       -- variable.
    | n == pos = __IMPOSSIBLE__

renameVarOnArgVar (Arg h def@(Def _ _)) pos = Arg h (renameVarsOnTerm def pos)
renameVarOnArgVar _ _ = __IMPOSSIBLE__

renameVarsOnTerm :: Term -> Nat -> Term
renameVarsOnTerm term@(Def _ [])  _   = term
renameVarsOnTerm (Def qName args) pos =
    Def qName $ map (`renameVarOnArgVar` pos) args
renameVarsOnTerm _ _ = __IMPOSSIBLE__

renameVarsOnCBody :: ClauseBody -> Nat -> ClauseBody
renameVarsOnCBody (Bind (Abs var cBody)) pos =
    Bind (Abs var (renameVarsOnCBody cBody pos))
renameVarsOnCBody (Body term) pos = Body $ renameVarsOnTerm term pos
renameVarsOnCBody _ _ = __IMPOSSIBLE__

-- To remove the binding on a proof term in a ClauseBody,
--
-- e.g. remove the binding on Nn : N n where D : Set, n : D and N : D → Set.
--
-- We know that the bounded variable is a proof term from the
-- invocation to this function.
removeBindingOnCBodyPos :: ClauseBody -> String -> Nat -> ClauseBody
removeBindingOnCBodyPos (Bind (Abs var1 cBody)) var2 pos =
    if var1 == var2
       then renameVarsOnCBody cBody pos -- We remove the bind and rename the
                                        -- variables inside the body.
       else removeBindingOnCBodyPos cBody var2 pos
removeBindingOnCBodyPos _ _ _ = __IMPOSSIBLE__

removeBindingOnCBody :: ClauseBody -> String -> ClauseBody
removeBindingOnCBody cBody var = removeBindingOnCBodyPos cBody var pos
    where
    pos :: Nat
    pos = posVarOnCBody cBody var
