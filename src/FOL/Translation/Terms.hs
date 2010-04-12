------------------------------------------------------------------------------
-- Translation from Agda *internal* terms to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module FOL.Translation.Terms where

------------------------------------------------------------------------------
-- Haskell imports
import Control.Monad.Trans.Class ( lift )
import Control.Monad.Trans.Reader ( ask, local )
import Control.Monad.Trans.State ( evalState )

------------------------------------------------------------------------------
-- Agda library imports
import Agda.Syntax.Abstract.Name ( nameConcrete, QName(QName) )
import Agda.Syntax.Common
    ( Arg(Arg)
    , argHiding
    , Hiding(Hidden, NotHidden)
    , unArg
    )
import qualified Agda.Syntax.Concrete.Name as C
    ( Name(Name, NoName)
    , NamePart(Id, Hole)
    )
import Agda.Syntax.Internal
    ( Abs(Abs)
    , Args
    , Sort(Type)
    , Term(Con, Def, Fun, Lam, Lit, MetaV, Pi, Sort, Var)
    , Type(El)
    )
import Agda.Syntax.Literal ( Literal(LitLevel) )
import Agda.Syntax.Position ( noRange )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

------------------------------------------------------------------------------
-- Local imports
import FOL.Constants
    ( trueFOL
    , falseFOL
    , notFOL
    , andFOL
    , orFOL
    , existsFOL
    , equalsFOL
    )
import FOL.Monad ( T )
import FOL.Primitives ( app, equal )
import FOL.Translation.Common ( AgdaTerm )
import {-# source #-} FOL.Translation.Types ( argTypeToFormula, typeToFormula )
import FOL.Types ( FormulaFOL(..), TermFOL(..))
import Utils.Names ( freshName )
import Reports ( reportSLn )

#include "../../undefined.h"

------------------------------------------------------------------------------

argTermToFormula :: Arg AgdaTerm -> T FormulaFOL
argTermToFormula Arg {argHiding = NotHidden, unArg = term} = termToFormula term
argTermToFormula Arg {argHiding = Hidden} =
    error "argTermToFormula: not implemented"

argTermToTermFOL :: Arg AgdaTerm -> T TermFOL
argTermToTermFOL (Arg _ term) = termToTermFOL term

binConst :: (FormulaFOL -> FormulaFOL -> FormulaFOL)
            -> Arg AgdaTerm
            -> Arg AgdaTerm
            -> T FormulaFOL
binConst op arg1 arg2 = do f1 <- argTermToFormula arg1
                           f2 <- argTermToFormula arg2
                           return $ op f1 f2

termToFormula :: AgdaTerm -> T FormulaFOL
termToFormula term@(Def (QName _ name) args) = do
    lift $ reportSLn "termToFormula" 10 $ "Processing term Def:\n" ++ show term

    let cName :: C.Name
        cName = nameConcrete name

    case cName of
      C.NoName{} -> __IMPOSSIBLE__

      C.Name{} ->
          case args of
            [] | isCNameConstFOL trueFOL  -> return TRUE

               | isCNameConstFOL falseFOL -> return FALSE

               | otherwise                -> return $ Predicate (show cName) []

            (a:[]) | isCNameConstFOL notFOL ->
                         do f <- argTermToFormula a
                            return $ Not f

                   | isCNameConstFOL existsFOL  ->
                     -- N.B. We should use the following guard if we use the
                     -- the FOL constant forAllFOL
                     -- ( isCNameConstFOL existsFOL ||
                     --   isCNameConstFOL forAllFOL )

                     -- Note: AgdaLight (Plugins.FOL.Translation) binds
                     -- a new variable to handle the quantifiers. We
                     -- didn't do it because we took the variable name
                     -- from the term Lam.

                     -- ToDo: Fix the possible name clash

                       do let p :: AgdaTerm
                              p = unArg a

                          let x :: String
                              x = case p of
                                    (Lam NotHidden (Abs sName _)) -> sName
                                    _ -> __IMPOSSIBLE__

                          fm <- termToFormula p

                          -- N.B. We should use the following test if
                          -- we use the the FOL constant forAllFOL
                          -- if isCNameConstFOL existsFOL
                          --    then return $ Exists x $ \_ -> fm
                          --    else return $ ForAll x $ \_ -> fm

                          return $ Exists x $ \_ -> fm

                   | otherwise -> do
                      -- In this guard we translate predicates with
                      -- one argument (e.x. P : D -> Set).

                      -- ToDo: To test if 'termToTermFOL (unArg a)'
                      -- works with implicit arguments.
                      t <- argTermToTermFOL a
                      return $ Predicate (show cName) [t]

            (a1:a2:[])
                | isCNameConstFOLTwoHoles andFOL     -> binConst And a1 a2

                -- We are not using the FOL constants impliesFOL
                -- isCNameConstFOLTwoHoles impliesFOL -> binConst Implies a1 a2

                | isCNameConstFOLTwoHoles orFOL      -> binConst Or a1 a2

                -- We are not using the FOL constants equivFOL
                -- isCNameConstFOLTwoHoles equivFOL   -> binConst Equiv a1 a2

                | isCNameConstFOLTwoHoles equalsFOL
                    -> do lift $ reportSLn "termToFormula" 20 "Processing equals"
                          t1 <- argTermToTermFOL a1
                          t2 <- argTermToTermFOL a2
                          return $ equal [t1, t2]

                | otherwise -> do
                      lift $ reportSLn "termToFormula" 20 $
                               "Processing a definition with two arguments which " ++
                               "is not a FOL constant"
                      t1 <- argTermToTermFOL a1
                      t2 <- argTermToTermFOL a2
                      return $ Predicate (show cName) [t1, t2]

            threeOrMore -> do
                      terms <- mapM argTermToTermFOL threeOrMore
                      return $ Predicate (show cName) terms

          where
            isCNameConstFOL :: String -> Bool
            isCNameConstFOL constFOL =
                -- The equality on the data type C.Name is defined
                -- to ignore ranges, so we use noRange.
                cName == C.Name noRange [C.Id constFOL]

            isCNameConstFOLTwoHoles :: String -> Bool
            isCNameConstFOLTwoHoles constFOL =
                -- The operators are represented by a list with Hole's.
                -- See the documentation for C.Name.
                cName == C.Name noRange [C.Hole, C.Id constFOL, C.Hole]

termToFormula term@(Fun tyArg ty) = do
  lift $ reportSLn "termToFormula" 10 $ "Processing term Fun:\n" ++ show term
  f1 <- argTypeToFormula tyArg
  f2 <- typeToFormula ty
  return $ Implies f1 f2

-- ToDo: To add test for this case.
termToFormula term@(Lam _ (Abs _ termLam)) = do
  lift $ reportSLn "termToFormula" 10 $ "Processing term Lam:\n" ++ show term

  vars <- ask

  let freshVar :: String
      freshVar = evalState freshName vars

  -- See the reason for the order in the enviroment in
  -- termToFormula term@(Pi ... )
  f <- local (\varNames -> freshVar : varNames) $ termToFormula termLam
  return f

termToFormula term@(Pi tyArg (Abs _ tyAbs)) = do
  lift $ reportSLn "termToFormula" 10 $ "Processing term Pi:\n" ++ show term

  vars <- ask

  let freshVar :: String
      freshVar = evalState freshName vars

  -- The de Bruijn indexes are assigned from "right to left", e.g.
  -- in '(A B C : Set) -> ...', A is 2, B is 1, and C is 0,
  -- so we need create the list in the same order.

  lift $ reportSLn "termToFormula" 20
           "Starting processing in local enviroment ..."
  f2 <- local (\varNames -> freshVar : varNames) $ typeToFormula tyAbs
  lift $ reportSLn "termToFormula" 20
           "Finalized processing in local enviroment"

  case unArg tyArg of
    -- The bounded variable is quantified on a Set (e.g. D : Set ⊢ d : D), so
    -- we translate without any problem.
    -- N.B. The pattern matching on (Def _ []).
    El (Type (Lit (LitLevel _ 0))) (Def _ []) -> do
                     return $ ForAll freshVar (\_ -> f2)

    -- The bound variable is quantified on a Predicate
    -- (e.g. D : Set, n : D, N : D → Set ⊢ Nn : N n).
    -- In this case, we erase the quantification and try it as a
    -- function type.  This solve the problem the translation of
    -- sN : {n : D} → (Nn : N n) → N (succ n).
    -- N.B. The pattern matching on (Def _ _).
    El (Type (Lit (LitLevel _ 0))) (Def _ _) -> do
       f1 <- argTypeToFormula tyArg
       return $ Implies f1 f2

    El (Type (Lit (LitLevel _ 0))) _ -> __IMPOSSIBLE__

    -- Old version
    -- ToDo: Check it
    -- The variable bound has type Set, i.e. a propositional constant.
    -- El (Type (Lit (LitLevel _ 1))) _ ->
        -- return $ ForAll freshVar (\_ -> f2)

    -- The bound variable is quantified on a Set₁ (e.g. A : Set).
    -- In this case, we erase the quantification and try it as a
    -- function type.
    El (Type (Lit (LitLevel _ 1))) (Sort _)  -> do
       lift $ reportSLn "termToFormula" 20 $
            "The type tyArg is: " ++ show tyArg
       return f2

    El (Type (Lit (LitLevel _ 1))) _ -> __IMPOSSIBLE__

    _                                -> __IMPOSSIBLE__

-- ToDo: To add test for this case.
termToFormula term@(Var n _) = do
  lift $ reportSLn "termToFormula" 10 $ "Processing term Var: " ++ show term

  vars <- ask

  if length vars <= fromIntegral n
     then __IMPOSSIBLE__
     else return $ Predicate (vars !! fromIntegral n) []

termToFormula (Con _ _)   = __IMPOSSIBLE__
termToFormula (Lit _)     = __IMPOSSIBLE__
termToFormula (MetaV _ _) = __IMPOSSIBLE__
termToFormula (Sort _)    = __IMPOSSIBLE__

-- Translate 'fn x1 ... xn' to 'kApp (... kApp (kApp(fn, x1), x2), ..., xn)'.
appArgs :: String -> Args -> T TermFOL
appArgs fn args = do
  termsFOL <- mapM argTermToTermFOL args
  return $ foldl (\x y -> app [x, y]) (FunFOL fn []) termsFOL

-- Translate an Agda term to an FOL term.
termToTermFOL :: AgdaTerm -> T TermFOL
-- Remark: The code for the cases Con and Def is very similar.
termToTermFOL term@(Con (QName _ name) args)  = do
  lift $ reportSLn "termToTermFOL" 10 $ "Processing term Con:\n" ++ show term

  let cName :: C.Name
      cName = nameConcrete name

  case cName of
    C.NoName{} -> __IMPOSSIBLE__

    C.Name _ [C.Id strName] ->
        case args of
          [] -> -- The term Con is a data constructor without arguments.
                -- It is translated as a FOL constant.
                return $ ConstFOL strName

          _ -> -- The term Con is a data constructor with arguments.
               -- The term is translated as a FOL function.
               appArgs strName args

    _ -> __IMPOSSIBLE__

termToTermFOL term@(Def (QName _ name) args) = do
  lift $ reportSLn "termToTermFOL" 10 $ "Processing term Def:\n" ++ show term

  let cName :: C.Name
      cName = nameConcrete name

  case cName of
    C.NoName{} -> __IMPOSSIBLE__

    -- The term Def doesn't have holes.
    C.Name _ [C.Id strName] ->
        case args of
          [] -> -- The term Def is a constructor.
                -- It is translated as a FOL constant.
                return $ ConstFOL strName

          _ -> -- The term Def is a function with arguments.
               appArgs strName args

    -- The term Def has holes.
    -- We use the parts of the name to produce a new function name,
    -- e.g. the function 'if_then_else_' is called 'ifthenelse'.
    C.Name _ nameParts -> appArgs (concatMap takeIds nameParts) args
       where
         takeIds :: C.NamePart -> String
         takeIds C.Hole = []
         takeIds (C.Id strName) = strName

termToTermFOL (Var n _) = do
  vars <- ask

  if length vars <= fromIntegral n
     then __IMPOSSIBLE__
     else return $ VarFOL (vars !! fromIntegral n)

termToTermFOL (Fun _ _)   = __IMPOSSIBLE__
termToTermFOL (Lam _ _)   = __IMPOSSIBLE__
termToTermFOL (Lit _)     = __IMPOSSIBLE__
termToTermFOL (MetaV _ _) = __IMPOSSIBLE__
termToTermFOL (Pi _ _)    = __IMPOSSIBLE__
termToTermFOL (Sort _)    = __IMPOSSIBLE__
