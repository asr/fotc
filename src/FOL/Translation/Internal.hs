------------------------------------------------------------------------------
-- Translation of Agda internal types to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module FOL.Translation.Internal where

-- Haskell imports
-- import Control.Monad.Trans.Reader ( ask, local )
-- import Control.Monad.Trans.State ( evalState )

-- Agda library imports
import Agda.Syntax.Internal
    ( Abs(Abs)
    , ClauseBody(Bind,Body)
    , Telescope(EmptyTel, ExtendTel)
    )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

-- Local imports
import FOL.Monad ( T )
import FOL.Translation.Terms ( termToFormula )
import FOL.Translation.Types ( argTypeToFormula )
import FOL.Types ( FormulaFOL )

#include "../../undefined.h"

------------------------------------------------------------------------------

telescopeToFormula :: Telescope -> T FormulaFOL
telescopeToFormula EmptyTel             = __IMPOSSIBLE__
telescopeToFormula (ExtendTel tyArg _ ) = argTypeToFormula tyArg

clauseBodyToFormula :: ClauseBody -> T FormulaFOL
clauseBodyToFormula (Body term )         = termToFormula term
clauseBodyToFormula (Bind (Abs _ cBody)) = clauseBodyToFormula cBody
clauseBodyToFormula _                    = __IMPOSSIBLE__
