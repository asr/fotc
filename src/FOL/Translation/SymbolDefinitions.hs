------------------------------------------------------------------------------
-- Translation of symbols's definitions to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module FOL.Translation.SymbolDefinitions where

-- Haskell imports
import Control.Monad.Trans.Reader ( ask, local )
import Control.Monad.Trans.State ( evalState )

-- Agda library imports
import Agda.Syntax.Common ( Arg(Arg) )
import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Internal
    ( Abs(Abs)
    , Clause(Clause)
    , ClauseBody
    , Sort(Type)
    , Telescope(ExtendTel)
    , Term(Def, Lit)
    , Type(El)
    )
import Agda.Syntax.Literal ( Literal(LitLevel) )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

-- Local imports
import FOL.Monad ( T )
import FOL.Translation.Common ( AgdaTerm, varsToArgs )
import FOL.Translation.Internal
    ( cBodyToFormula
    , removeQuantificationOnCBody
    )
import FOL.Translation.Terms ( termToFormula )
import FOL.Types ( FormulaFOL(Equiv, ForAll) )
import Utils.Names ( freshName )

#include "../../undefined.h"

------------------------------------------------------------------------------

-- ToDo: At the moment, it is only allowed to translate symbols with
-- one clause.
symDefToFormula :: QName -> [Clause] -> T FormulaFOL
symDefToFormula _      []        = __IMPOSSIBLE__
symDefToFormula qname  (cl : []) = symClauseToFormula qname cl
symDefToFormula _      _         = __IMPOSSIBLE__


-- A clause is defined by (Agda.Syntax.Internal)
-- data Clause = Clause
--     { clauseRange     :: Range
--     , clauseTel       :: Telescope
--     , clausePerm      :: Permutation
--     , clausePats      :: [Arg Pattern]
--     , clauseBody      :: ClauseBody
--     }

symClauseToFormula :: QName -> Clause -> T FormulaFOL
-- In this equation we generate an universal quantification
-- on an equal number of variables to length [Arg Pattern].
symClauseToFormula qname (Clause r tel perm (_ : pats) cBody ) = do
  case tel of
    -- The binding variable is quantified on a Set (e.g. D : Set ⊢ d : D), so
    -- we translate without any problem.
    -- N.B. The pattern matching on (Def _ []).
    ExtendTel
      (Arg _ (El (Type (Lit (LitLevel _ 0))) (Def _ [])))
      (Abs _ tels) -> do
          vars <- ask

          let freshVar :: String
              freshVar = evalState freshName vars

          -- See the reason for the order in the enviroment in
          -- FOL.Translation.Terms.termToFormula term@(Pi ... )
          f <- local (\varNames -> freshVar : varNames) $
               symClauseToFormula qname (Clause r tels perm pats cBody )

          return $ ForAll freshVar (\_ -> f)

    -- The binding variable is quantified on a Predicate
    -- (e.g. D : Set, n : D, N : D → Set ⊢ Nn : N n)
    -- so we need remove this quantification.
    -- N.B. The pattern matching on (Def _ _).
    ExtendTel
      (Arg _ (El (Type (Lit (LitLevel _ 0))) (Def _ _)))
      (Abs var tels) -> do
             let newBody :: ClauseBody
                 newBody = removeQuantificationOnCBody cBody var
             symClauseToFormula qname (Clause r tels perm pats newBody )

    _ -> __IMPOSSIBLE__

symClauseToFormula qname (Clause _ _ _ [] cBody ) = do

  vars <- ask

  -- We create the Agda term corresponds to the LHS of the symbol's
  -- definition.
  let lhs :: AgdaTerm
      lhs = Def qname $ varsToArgs $ fromIntegral $ length vars

  lhsF <- termToFormula lhs

  -- The RHS is the body of the clause
  rhsF <- cBodyToFormula cBody

  -- The LHS and RHS terms are related via an equivalence logic.
  -- ToDo: What happens if the symbol is a function definition?
  return $ Equiv lhsF rhsF
