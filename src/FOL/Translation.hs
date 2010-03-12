{-# LANGUAGE CPP #-}

module FOL.Translation where

-- import Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Syntax.Position ( noRange )
import Agda.Utils.Impossible ( Impossible(..), throwImpossible )

-- import Control.Monad.State ( get, put )
import Control.Monad.Reader ( ask, local )
import Control.Monad.State

import FOL.Constants
import FOL.Primitives ( app, equal )
import FOL.Types

import Monad

import Reports ( reportLn )

#include "../undefined.h"

type AgdaType = Type
type AgdaTerm = Term

varInTerm :: AgdaTerm -> [String]
varInTerm (Pi _ (Abs strName (El _ _))) = [strName]
varInTerm _                          = __IMPOSSIBLE__

varInType :: AgdaType -> [String]
varInType (El (Type _ ) term) = varInTerm term
varInType _                   = __IMPOSSIBLE__

typeToFormula :: AgdaType -> T Formula
typeToFormula ty@(El (Type _ ) term) =
    do reportLn "typeToFormula" 10 $ "Processing type ty:\n" ++ show ty
       termToFormula term
typeToFormula _                   = __IMPOSSIBLE__

argTypeToFormula :: Arg AgdaType -> T Formula
argTypeToFormula Arg {argHiding = NotHidden, unArg = ty} = typeToFormula ty
argTypeToFormula Arg {argHiding = Hidden} =
    error "argTypeToFormula: not implemented"

argTermToFormula :: Arg AgdaTerm -> T Formula
argTermToFormula Arg {argHiding = NotHidden, unArg = term} = termToFormula term
argTermToFormula Arg {argHiding = Hidden} =
    error "argTermToFormula: not implemented"

argTermToFOLTerm :: Arg AgdaTerm -> T FOLTerm
argTermToFOLTerm Arg {argHiding = NotHidden, unArg = term} = termToFOLTerm term
argTermToFOLTerm Arg {argHiding = Hidden} =
    error "argTermToFOLTerm: not implemented"

binConst :: (Formula -> Formula -> Formula)
            -> Arg AgdaTerm
            -> Arg AgdaTerm
            -> T Formula
binConst op arg1 arg2 = do f1 <- argTermToFormula arg1
                           f2 <- argTermToFormula arg2
                           return $ op f1 f2

termToFormula :: AgdaTerm -> T Formula
termToFormula term@(Def (QName _ name) args) = do
    reportLn "termToFormula" 10 $ "Processing term Def:\n" ++ show term

    let cName :: C.Name
        cName = nameConcrete name

    case cName of
      C.NoName{} -> __IMPOSSIBLE__

      C.Name{} ->
          case args of
            [] | isCNameFOLConst folTrue  -> return TRUE

               | isCNameFOLConst folFalse -> return FALSE

               | otherwise                -> __IMPOSSIBLE__

            (a:[]) | isCNameFOLConst folNot ->
                         do f <- argTermToFormula a
                            return $ Not f

                   | (isCNameFOLConst folExists ||
                      isCNameFOLConst folForAll)  ->
                     -- Note: AgdaLight (Plugins.FOL.Translation) binds
                     -- a new variable to handle the quantifiers. We
                     -- didn't do it because we took the variable name
                     -- from the term Lam.

                       do let p :: AgdaTerm
                              p = unArg a

                          let x :: String
                              x = case p of
                                    (Lam NotHidden (Abs sName _)) -> sName
                                    _ -> __IMPOSSIBLE__

                          fm <- termToFormula p

                          if isCNameFOLConst folExists
                             then return $ Exists x $ \_ -> fm
                             else return $ ForAll x $ \_ -> fm

                   | otherwise -> __IMPOSSIBLE__

            (a1:a2:[])
                | isCNameFOLConstTwoHoles folAnd -> binConst And a1 a2

                | isCNameFOLConstTwoHoles folImplies -> binConst Implies a1 a2

                | isCNameFOLConstTwoHoles folOr -> binConst Or a1 a2

                | isCNameFOLConstTwoHoles folEquiv -> binConst Equiv a1 a2

                | isCNameFOLConstTwoHoles folEquals
                    -> do reportLn "termToFormula" 20 $ "Processing equals"
                          t1 <- argTermToFOLTerm a1
                          t2 <- argTermToFOLTerm a2
                          return $ equal [t1, t2]

                | otherwise -> __IMPOSSIBLE__

            _ ->  __IMPOSSIBLE__

          where
            isCNameFOLConst :: String -> Bool
            isCNameFOLConst folConst =
                -- The equality on the data type C.Name is defined
                -- to ignore ranges, so we use noRange.
                cName == C.Name noRange [C.Id folConst]

            isCNameFOLConstTwoHoles :: String -> Bool
            isCNameFOLConstTwoHoles folConst =
                -- The operators are represented by a list with Hole's.
                -- See the documentation for C.Name.
                cName == C.Name noRange [C.Hole, C.Id folConst, C.Hole]

termToFormula term@(Fun tyArg ty) = do
  reportLn "termToFormula" 10 $ "Processing term Fun:\n" ++ show term
  f1 <- argTypeToFormula tyArg
  f2 <- typeToFormula ty
  return $ Implies f1 f2

termToFormula term@(Lam _ (Abs strName termLam)) = do
  reportLn "termToFormula" 10 $ "Processing term Lam:\n" ++ show term

  f <- local (\(a, vars) -> (a, strName : vars)) $ termToFormula termLam
  return f

termToFormula term@(Pi tyArg (Abs strName tyAbs)) = do
  reportLn "termToFormula" 10 $ "Processing term Pi:\n" ++ show term

  -- The de Bruijn indexes are assigned from "right to left", e.g.
  -- in '(A B C : Set) -> ...', A is 2, B is 1, and C is 0,
  -- so we need create the list in the same "order".
  f <- local (\(a, vars) -> (a, strName : vars)) $ typeToFormula tyAbs
  case unArg tyArg of
     -- The varible bound has type below Set (e.g. D : Set).
    (El (Type (Lit (LitLevel _ 0))) _) ->
                       return $ ForAll strName (\_  -> f)
    -- The variable bound has type Set, i.e. a propositional constant.
    (El (Type (Lit (LitLevel _ 1))) _) ->
                       return f

    _               -> __IMPOSSIBLE__


termToFormula term@(Var n _) = do
  reportLn "termToFormula" 10 $ "Processing term Var: " ++ show term

  (_, vars) <- ask

  if length vars <= fromIntegral n
     then __IMPOSSIBLE__
     else return $ Predicate (vars !! fromIntegral n) []

termToFormula _ = error "termToFormula: not implemented"


-- Translate 'fn x1 ... xn' to 'kApp (... kApp (kApp(fn, x1), x2), ..., xn)'.
appArgs :: String -> Args -> T FOLTerm
appArgs fn args = do
  folTerms <- mapM argTermToFOLTerm args
  return $ foldl (\x y -> app [x,y]) (FOLFun fn []) folTerms

-- Translate an Agda term to an FOL term
termToFOLTerm :: AgdaTerm -> T FOLTerm
termToFOLTerm (Var n _) = do
  (_, vars) <- ask

  if length vars <= fromIntegral n
     then __IMPOSSIBLE__
     else return $ FOLVar (vars !! fromIntegral n)


-- Remark: The code for the cases Con and Def is very similar.
termToFOLTerm term@(Con (QName _ name) args)  = do
  reportLn "termToFOLTerm" 10 $ "Processing term Con:\n" ++ show term

  let cName :: C.Name
      cName = nameConcrete name

  case cName of
    C.NoName{}              -> __IMPOSSIBLE__

    C.Name _ [C.Id strName] ->
        case args of
          [] -> -- The term Con is a data constructor without arguments.
                -- It is translated as a FOL constant.
                return $ FOLConst strName

          _ -> -- The term Con is a data constructor with arguments.
               -- The term is translated as a FOL function.
               appArgs strName args

    _ -> __IMPOSSIBLE__

termToFOLTerm term@(Def (QName _ name) args) = do
  reportLn "termToFOLTerm" 10 $ "Processing term Def:\n" ++ show term

  let cName :: C.Name
      cName = nameConcrete name

  case cName of
    C.NoName{} -> __IMPOSSIBLE__

    -- The term Def doesn't have holes.
    C.Name _ [C.Id strName] ->
        case args of
          [] -> -- The term Def is a constructor.
                -- It is translated as a FOL constant.
                return $ FOLConst strName

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

termToFOLTerm _ = error "termToFOLTerm: not implemented"
