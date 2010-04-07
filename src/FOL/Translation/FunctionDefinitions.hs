------------------------------------------------------------------------------
-- Translation of function's definitions to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module FOL.Translation.FunctionDefinitions where

-- Haskell imports
import Control.Monad.Trans.Reader ( ask, local )
import Control.Monad.Trans.State ( evalState )

-- Agda library imports
import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Internal ( Clause(Clause) )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

-- Local imports
import FOL.Monad ( T )
import FOL.Translation.Internal ( clauseBodyToFormula )
-- import FOL.Translation.Terms ( termToFormula )
import FOL.Types ( FormulaFOL(ForAll) )
import Utils.Names ( freshName )

#include "../../undefined.h"

------------------------------------------------------------------------------

fnDefToFormula :: QName -> [Clause] -> T FormulaFOL
fnDefToFormula _      []        = __IMPOSSIBLE__
fnDefToFormula qname  (cl : []) = fnClauseToFormula qname cl
fnDefToFormula _      _         = __IMPOSSIBLE__

fnClauseToFormula :: QName -> Clause -> T FormulaFOL
fnClauseToFormula qname (Clause r tel perm (_ : patArs) cBody ) = do
  vars <- ask

  let freshVar :: String
      freshVar = evalState freshName vars

  -- See the reason for the order in the enviroment in
  -- FOL.Translation.Terms.termToFormula term@(Pi ... )
  f <- local (\varNames -> freshVar : varNames) $
       fnClauseToFormula qname (Clause r tel perm patArs cBody )
  return $ ForAll freshVar (\_ -> f)

fnClauseToFormula _ (Clause _ _ _ [] cBody ) = clauseBodyToFormula cBody
