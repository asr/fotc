------------------------------------------------------------------------------
-- Translation of Agda internal types to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module FOL.Translation.Internal where

-- Haskell imports
-- import Control.Monad.Trans.Reader ( ask, local )
-- import Control.Monad.Trans.State ( evalState )

-- Agda library imports
import Agda.Syntax.Common ( Arg(Arg), Nat )
import Agda.Syntax.Internal
    ( Abs(Abs)
    , ClauseBody(Bind,Body)
    , Telescope(EmptyTel, ExtendTel)
    , Term(Def, Var)
    )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

-- Local imports
import FOL.Monad ( T )
import FOL.Translation.Terms ( termToFormula, termToTermFOL )
import FOL.Translation.Types ( argTypeToFormula )
import FOL.Types ( FormulaFOL, TermFOL )

#include "../../undefined.h"

------------------------------------------------------------------------------

telescopeToFormula :: Telescope -> T FormulaFOL
telescopeToFormula EmptyTel             = __IMPOSSIBLE__
telescopeToFormula (ExtendTel tyArg _ ) = argTypeToFormula tyArg

cBodyToFormula :: ClauseBody -> T FormulaFOL
cBodyToFormula (Body term )         = termToFormula term
cBodyToFormula (Bind (Abs _ cBody)) = cBodyToFormula cBody
cBodyToFormula _                    = __IMPOSSIBLE__

cBodyToTermFOL :: ClauseBody -> T TermFOL
cBodyToTermFOL (Body term )         = termToTermFOL term
cBodyToTermFOL (Bind (Abs _ cBody)) = cBodyToTermFOL cBody
cBodyToTermFOL _                    = __IMPOSSIBLE__

------------------------------------------------------------------------------
-- To remove the quantification over on proof term
-- (e.g. (e.g. D : Set, n : D, N : D → Set ⊢ Nn : N n)
-- in an ClauseBody.

posVarOnCBody :: ClauseBody -> String -> Nat
posVarOnCBody (Bind (Abs var1 cBody)) var2
    | var1 == var2 = 0
    | otherwise    = 1 + posVarOnCBody cBody var2

-- In other cases it hasn't sense. In addition, we must find the
-- variable before reach the Body.
posVarOnCBody _ _ = __IMPOSSIBLE__

updateVarOnArgVar :: Arg Term -> Nat -> Arg Term
updateVarOnArgVar var@(Arg h (Var n [])) pos
    | n < pos = var -- The variable was before than the quantified
                    -- variable, we don't do nothing.
    | n > pos = (Arg h (Var (n - 1) [])) -- The variable was after
                                         -- than the quantified
                                         -- variable, we need
                                         -- "unbound" the quantified
                                         -- variable.
    | n == pos = __IMPOSSIBLE__

updateVarOnArgVar _ _ = __IMPOSSIBLE__

updateVarsOnTerm :: Term -> Nat -> Term
updateVarsOnTerm term@(Def _ [])  _   = term
updateVarsOnTerm (Def qName args) pos =
    Def qName $ map (flip updateVarOnArgVar pos) args
updateVarsOnTerm _ _ = __IMPOSSIBLE__

updateVarsOnCBody :: ClauseBody -> Nat -> ClauseBody
updateVarsOnCBody (Bind (Abs name cBody)) pos =
    Bind (Abs name (updateVarsOnCBody cBody pos))
updateVarsOnCBody (Body term) pos =
    Body (updateVarsOnTerm term pos)
updateVarsOnCBody _ _ = __IMPOSSIBLE__

removeQuantificationOnCBody :: ClauseBody -> String -> ClauseBody
removeQuantificationOnCBody cBody var = updateVarsOnCBody cBody pos
  where
    pos :: Nat
    pos = posVarOnCBody cBody var

------------------------------------------------------------------------------