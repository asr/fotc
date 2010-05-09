------------------------------------------------------------------------------
-- Translation from Agda *internal* terms to FOL formulas
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}

module FOL.Translation.Internal.Terms where

------------------------------------------------------------------------------
-- Haskell imports
-- import Control.Monad.IO.Class ( liftIO )
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
import FOL.Translation.Concrete.Name ( concatName )
import {-# source #-} FOL.Translation.Internal.Types ( typeToFormula )
import FOL.Types ( FormulaFOL(..), TermFOL(..))
import Utils.Names ( freshName )
import Reports ( reportSLn )

#include "../../../undefined.h"

------------------------------------------------------------------------------

argTermToFormula :: Arg AgdaTerm -> T FormulaFOL
argTermToFormula Arg {argHiding = NotHidden, unArg = term} = termToFormula term
argTermToFormula Arg {argHiding = Hidden} =
    error "argTermToFormula: not implemented"

binConst :: (FormulaFOL -> FormulaFOL -> FormulaFOL)
            -> Arg AgdaTerm
            -> Arg AgdaTerm
            -> T FormulaFOL
binConst op arg1 arg2 = do f1 <- argTermToFormula arg1
                           f2 <- argTermToFormula arg2
                           return $ op f1 f2

termToFormula :: AgdaTerm -> T FormulaFOL
termToFormula term@(Def (QName _ name) args) = do
    lift $ reportSLn "termToFormula" 10 $
             "Processing termToFormula Def:\n" ++ show term

    let cName :: C.Name
        cName = nameConcrete name

    case cName of
      C.NoName{} -> __IMPOSSIBLE__

      C.Name _ [] -> __IMPOSSIBLE__

      C.Name{} ->
          case args of
            [] | isCNameConstFOL trueFOL  -> return TRUE

               | isCNameConstFOL falseFOL -> return FALSE

               | otherwise                -> return $ Predicate (show cName) []

            (a:[]) | isCNameConstFOL notFOL ->
                         do f <- argTermToFormula a
                            return $ Not f

                   | isCNameConstFOL existsFOL  -> do
                       lift $ reportSLn "termToFormula" 20 "The cName is existsFOL"
                     -- N.B. We should use the following guard if we use the
                     -- the FOL constant forAllFOL
                     -- ( isCNameConstFOL existsFOL ||
                     --   isCNameConstFOL forAllFOL )

                       fm <- termToFormula $ unArg a

                       -- N.B. We should use the following test if
                       -- we use the the FOL constant forAllFOL
                       -- if isCNameConstFOL existsFOL
                       --    then return $ Exists freshVar $ \_ -> fm
                       --    else return $ ForAll freshVar $ \_ -> fm

                       vars <- ask

                       let freshVar :: String
                           freshVar = evalState freshName vars

                       return $ Exists freshVar $ \_ -> fm

                   | otherwise -> do
                      -- In this guard we translate predicates with
                      -- one argument (e.g. P : D -> Set).

                      -- TODO: To test if 'termToTermFOL (unArg a)'
                      -- works with implicit arguments.
                      t <- termToTermFOL $ unArg a
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
                          t1 <- termToTermFOL $ unArg a1
                          t2 <- termToTermFOL $ unArg a2
                          return $ equal [t1, t2]

                | otherwise -> do
                      lift $ reportSLn "termToFormula" 20 $
                               "Processing a definition with two arguments which " ++
                               "is not a FOL constant: " ++ show cName
                      t1 <- termToTermFOL $ unArg a1
                      t2 <- termToTermFOL $ unArg a2
                      return $ Predicate (show cName) [t1, t2]

            threeOrMore -> do
                      terms <- mapM (termToTermFOL . unArg ) threeOrMore
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
  lift $ reportSLn "termToFormula" 10 $
           "Processing termToFormula Fun:\n" ++ show term
  f1 <- typeToFormula $ unArg tyArg
  f2 <- typeToFormula ty
  return $ Implies f1 f2

-- TODO: To add test for this case.
termToFormula term@(Lam _ (Abs _ termLam)) = do
  lift $ reportSLn "termToFormula" 10 $
           "Processing termToFormula Lam:\n" ++ show term

  vars <- ask

  let freshVar :: String
      freshVar = evalState freshName vars

  -- See the reason for the order in the enviroment in
  -- termToFormula term@(Pi ... ).
  f <- local (\varNames -> freshVar : varNames) $ termToFormula termLam
  return f

termToFormula term@(Pi tyArg (Abs _ tyAbs)) = do
  lift $ reportSLn "termToFormula" 10 $
           "Processing termToFormula Pi:\n" ++ show term

  vars <- ask

  let freshVar :: String
      freshVar = evalState freshName vars

  lift $ reportSLn "termToFormula" 20 $
           "Starting processing in local enviroment using the type:\n" ++
           show tyAbs

  -- The de Bruijn indexes are assigned from "right to left", e.g.
  -- in '(A B C : Set) -> ...', A is 2, B is 1, and C is 0,
  -- so we need create the list in the same order.
  f2 <- local (\varNames -> freshVar : varNames) $ typeToFormula tyAbs

  lift $ reportSLn "termToFormula" 20 $
           "Finalized processing in local enviroment using the type:\n" ++
           show tyAbs

  case unArg tyArg of
    -- The bounded variable is quantified on a Set (e.g. D : Set ⊢ d : D), so
    -- we translate without any problem.
    -- N.B. The pattern matching on (Def _ []).
    El (Type (Lit (LitLevel _ 0))) (Def _ []) ->
        return $ ForAll freshVar (\_ -> f2)

    -- The bounded variable is quantified on a Predicate
    -- (e.g. D : Set, n : D, N : D → Set ⊢ Nn : N n).
    -- In this case, we erase the quantification and try it as a
    -- function type.  This solve the problem of the translation of
    -- sN : {n : D} → (Nn : N n) → N (succ n).
    -- N.B. The pattern matching on (Def _ _).
    El (Type (Lit (LitLevel _ 0))) def@(Def _ _) -> do
       lift $ reportSLn "termToFormula" 20 $
           "Removing a quantification on the predicate:\n" ++ show def
       f1 <- typeToFormula $ unArg tyArg
       return $ Implies f1 f2

    -- Hack: The bounded variable is quantified on a function of a Set
    -- to a Set (e.g. D : Set ⊢ f : D → D). In this case we handle the
    -- bounded variable/function as a FOL variable
    -- (see termToTermFOL term@(Var n args)),
    -- and we quantified on this variable.
    El (Type (Lit (LitLevel _ 0)))
       (Fun (Arg _ (El (Type (Lit (LitLevel _ 0))) (Def _ [])))
            (El (Type (Lit (LitLevel _ 0))) (Def _ []))
       ) -> do
      lift $ reportSLn "termToFormula" 20 $
           "Processing bounded varible quantified on a function of a Set to a Set"
      return $ ForAll freshVar (\_ -> f2)

    El (Type (Lit (LitLevel _ 0))) _ -> __IMPOSSIBLE__

    -- Old version
    -- TODO: Check it
    -- The variable bound has type Set, i.e. a propositional constant.
    -- El (Type (Lit (LitLevel _ 1))) _ ->
        -- return $ ForAll freshVar (\_ -> f2)

    -- The bound variable is quantified on a Set₁ (e.g. A : Set).
    -- In this case, we erase the quantification.
    El (Type (Lit (LitLevel _ 1))) (Sort _)  -> do
       lift $ reportSLn "termToFormula" 20 $
            "The type tyArg is: " ++ show tyArg
       return f2

    El (Type (Lit (LitLevel _ 1))) _ -> __IMPOSSIBLE__

    _                                -> __IMPOSSIBLE__

-- TODO: To add test for this case.
termToFormula term@(Var n _) = do
  lift $ reportSLn "termToFormula" 10 $
           "Processing termToFormula Var: " ++ show term

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
  termsFOL <- mapM (termToTermFOL . unArg) args
  return $ foldl (\x y -> app [x, y]) (FunFOL fn []) termsFOL

-- Translate an Agda term to an FOL term.
termToTermFOL :: AgdaTerm -> T TermFOL
-- TODO: The code for the cases Con and Def is similar.
termToTermFOL term@(Con (QName _ name) args)  = do
  lift $ reportSLn "termToTermFOL" 10 $
           "Processing termToTermFOL Con:\n" ++ show term

  let cName :: C.Name
      cName = nameConcrete name

  case cName of
    C.NoName{}  -> __IMPOSSIBLE__

    C.Name _ [] -> __IMPOSSIBLE__

    -- The term Con doesn't have holes.
    C.Name _ [C.Id str] ->
        case args of
          [] -> -- The term Con is a data constructor without arguments.
                -- It is translated as a FOL constant.
                return $ ConstFOL str

          _ -> -- The term Con is a data constructor with arguments.
               -- It is translated as a FOL function.
               appArgs str args

    -- The term Con has holes. It is translated as a FOL function.
    C.Name _ parts -> do
      case args of
        [] -> __IMPOSSIBLE__
        _  -> appArgs (concatName parts) args

termToTermFOL term@(Def (QName _ name) args) = do
  lift $ reportSLn "termToTermFOL" 10 $
           "Processing termToTermFOL Def:\n" ++ show term

  let cName :: C.Name
      cName = nameConcrete name

  case cName of
    C.NoName{}  -> __IMPOSSIBLE__

    C.Name _ [] -> __IMPOSSIBLE__

    -- The term Def doesn't have holes.
    C.Name _ [C.Id str] ->
        case args of
          [] -> -- The term Def is a constructor.
                -- It is translated as a FOL constant.
                return $ ConstFOL str

          _ -> -- The term Def is a function with arguments.
               -- It is translated as a FOL function.
               appArgs str args

    -- The term Def has holes. It is translated as a FOL function.
    C.Name _ parts -> do
      case args of
        [] -> __IMPOSSIBLE__
        _  -> appArgs (concatName parts) args

termToTermFOL term@(Var n args) = do
  lift $ reportSLn "termToTermFOL" 10 $
           "Processing termToTermFOL Var:\n" ++ show term

  vars <- ask

  if length vars <= fromIntegral n
     then __IMPOSSIBLE__
     else do
       case args of
         [] -> return $ VarFOL (vars !! fromIntegral n)

         -- Hack: If we have a bounded variable quantified on a
         -- function of a Set to a Set, for example, the variable 'f'
         -- in '(f : D → D) → (a : D) → (lam f) ∙ a ≡ f a'
         -- we are quantifying on this variable
         -- (see termToFormula term@(Pi tyArg (Abs _ tyAbs))),
         -- therefore we need to apply this
         -- variable/function to a term.

         ((Arg _ (Var m _)) : [])  ->
             return $ app [(VarFOL (vars !! fromIntegral n))
                          , (VarFOL (vars !! fromIntegral m))
                          ]
         _  -> __IMPOSSIBLE__

termToTermFOL (Fun _ _)   = __IMPOSSIBLE__
termToTermFOL (Lam _ _)   = __IMPOSSIBLE__
termToTermFOL (Lit _)     = __IMPOSSIBLE__
termToTermFOL (MetaV _ _) = __IMPOSSIBLE__
termToTermFOL (Pi _ _)    = __IMPOSSIBLE__
termToTermFOL (Sort _)    = __IMPOSSIBLE__
