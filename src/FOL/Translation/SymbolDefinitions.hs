------------------------------------------------------------------------------
-- Translation of symbols's definitions to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module FOL.Translation.SymbolDefinitions where

-- Haskell imports
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.Error ( throwError )
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
import FOL.Primitives ( equal )
import FOL.Translation.Common ( AgdaTerm, AgdaType, varsToArgs )
import FOL.Translation.Internal.Internal
    ( cBodyToFormula
    , cBodyToTermFOL
    , removeQuantificationOnCBody
    )
import FOL.Translation.Internal.Terms ( termToFormula, termToTermFOL )
import FOL.Types ( FormulaFOL(Equiv, ForAll) )
import Utils.Names ( freshName )

#include "../../undefined.h"

------------------------------------------------------------------------------

symDefToFormula :: QName -> Type -> [Clause] -> T FormulaFOL
symDefToFormula _      _  []        = __IMPOSSIBLE__
symDefToFormula qName  ty (cl : []) = symClauseToFormula qName ty cl
symDefToFormula qName  _  _         =
    lift $ throwError $ "Error translating the symbol " ++ show qName ++
                        ". The definitions only can have a clause."

-- A clause is defined by (Agda.Syntax.Internal)
-- data Clause = Clause
--     { clauseRange     :: Range
--     , clauseTel       :: Telescope
--     , clausePerm      :: Permutation
--     , clausePats      :: [Arg Pattern]
--     , clauseBody      :: ClauseBody
--     }

symClauseToFormula :: QName -> AgdaType -> Clause -> T FormulaFOL
-- In this equation we generate an universal quantification
-- on an equal number of variables to length [Arg Pattern].
symClauseToFormula qName ty (Clause r tel perm (_ : pats) cBody ) =
  case tel of
    -- The bounded variable is quantified on a Set (e.g. D : Set ⊢ d : D), so
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
                 symClauseToFormula qName ty (Clause r tels perm pats cBody)

          return $ ForAll freshVar (\_ -> f)

    -- The bound variable is quantified on a Predicate
    -- (e.g. D : Set, n : D, N : D → Set ⊢ Nn : N n)
    -- so we need remove this quantification.
    -- N.B. The pattern matching on (Def _ _).
    ExtendTel
      (Arg _ (El (Type (Lit (LitLevel _ 0))) (Def _ _)))
      (Abs var tels) -> do
             let newBody :: ClauseBody
                 newBody = removeQuantificationOnCBody cBody var
             symClauseToFormula qName ty (Clause r tels perm pats newBody )

    _ -> __IMPOSSIBLE__

symClauseToFormula qName ty (Clause _ _ _ [] cBody ) = do

  vars <- ask

  -- We create the Agda term corresponds to the LHS of the symbol's
  -- definition.
  let lhs :: AgdaTerm
      lhs = Def qName $ varsToArgs $ fromIntegral $ length vars

  case ty of
    -- The defined symbol is a predicate
    El (Type (Lit (LitLevel _ 1))) _ -> do
            lhsF <- termToFormula lhs

            -- The RHS is the body of the clause
            rhsF <- cBodyToFormula cBody

            -- Because the LHS and RHS are formulas, they are
            -- related via an equivalence logic.
            return $ Equiv lhsF rhsF

    -- The defined symbol is a function
    El (Type (Lit (LitLevel _ 0))) _ -> do
            lhsT <- termToTermFOL lhs

            -- The RHS is the body of the clause
            rhsT <- cBodyToTermFOL cBody

            -- Because the LHS and RHS are terms, they are related via
            -- the equality.
            return $ equal [lhsT, rhsT]

    _ -> __IMPOSSIBLE__
