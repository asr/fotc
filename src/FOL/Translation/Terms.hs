------------------------------------------------------------------------------
-- |
-- Module      : FOL.Translation.Internal.Terms
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Translation from Agda internal terms to first-order logic formulae.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

module FOL.Translation.Terms
  ( termToFormula
  , termToFOLTerm
  ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad ( liftM2, when )
import Control.Monad.Error ( MonadError(throwError) )

import Data.List ( foldl' )

------------------------------------------------------------------------------
-- Agda library imports

import Agda.Syntax.Abstract.Name ( Name(nameConcrete, nameId) , QName(QName) )

import Agda.Syntax.Common
  ( Arg(Arg, argHiding, unArg)
  , Dom(Dom, unDom)
  , Hiding(Hidden, Instance, NotHidden)
  , NameId(NameId)
  , Nat
  )

import qualified Agda.Syntax.Concrete.Name as C
  ( Name(Name, NoName)
  , NamePart(Id, Hole)
  )

import Agda.Syntax.Internal
  ( Abs(Abs, NoAbs)
  , Args
  , Level(Max)
  , PlusLevel(ClosedLevel)
  , Sort(Type)
  , Term(Con, Def, DontCare, Lam, Level, Lit, MetaV, Pi, Sort, Var)
  , Type(El)
  )

import Agda.Syntax.Position  ( noRange )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )
import Agda.Utils.Monad      ( unlessM )

------------------------------------------------------------------------------
-- Local imports

import AgdaInternal.Interface ( isATPDefinition, qNameDefinition )

import FOL.Constants
  ( folTrue, folFalse, folNot, folAnd, folOr
  , folImplies, folEquiv, folExists, folForAll, folEquals
  )

import FOL.Primitives       ( appFn, appP, equal )
import FOL.Translation.Name ( concatName )

import {-# source #-} FOL.Translation.Types
  ( domTypeToFormula
  , typeToFormula
  )

import FOL.Types
  ( FOLFormula(TRUE, FALSE, Predicate, Not, And, Or, Implies, Equiv, ForAll, Exists)
  , FOLTerm(FOLFun, FOLVar)
  )

import Monad.Base
  ( getTVars
  , getTOpt
  , newTVar
  , popTVar
  , pushTVar
  , T
  )

import Monad.Reports ( reportSLn )

import Options
 ( Options( optNonFOLFormula
          , optNonFOLFunction
          , optNonFOLPropositionalFunction
          )
 )

#include "../../undefined.h"

------------------------------------------------------------------------------

qName2String ∷ QName → T String
qName2String qName@(QName _ name) = do
  def ← qNameDefinition qName

  -- Because the ATP pragma definitions are global, we need an unique
  -- name. In this case, we append to the @qName@ the @qName@'s id (it
  -- generates long TPTP name for the definitions).
  if isATPDefinition def
    then do
      let qNameId ∷ NameId
          qNameId = nameId name

      reportSLn "qName2String" 20 $ "qNameId : " ++ show qNameId

      case qNameId of
        NameId x i → return $ show (nameConcrete name) ++ "_"
                              ++ show x ++ "_"
                              ++ show i
    else return $ show $ nameConcrete name

-- We keep the three equations for debugging.
argTermToFormula ∷ Arg Term → T FOLFormula
argTermToFormula Arg {argHiding = Instance}             = __IMPOSSIBLE__
argTermToFormula Arg {argHiding = Hidden}               = __IMPOSSIBLE__
argTermToFormula Arg {argHiding = NotHidden, unArg = t} = termToFormula t

-- We keep the three equations for debugging.
argTermToFOLTerm ∷ Arg Term → T FOLTerm
argTermToFOLTerm Arg {argHiding = Instance}             = __IMPOSSIBLE__
argTermToFOLTerm Arg {argHiding = Hidden, unArg = t}    = termToFOLTerm t
argTermToFOLTerm Arg {argHiding = NotHidden, unArg = t} = termToFOLTerm t

binConst ∷ (FOLFormula → FOLFormula → FOLFormula) →
           Arg Term →
           Arg Term →
           T FOLFormula
binConst op arg1 arg2 =
  liftM2 op (argTermToFormula arg1) (argTermToFormula arg2)

-- We translate n-ary predicates. For example, the predicate
--
-- @P : D → D → D → Set@
--
-- is translated to @kAppP3(p,x,y,z)@, where @kAppP3@ is a hard-coded 4-ary
-- predicate symbol.
predicate ∷ QName → Args → T FOLFormula
predicate qName args = do
  folName ← qName2String qName
  case length args of
    0 → __IMPOSSIBLE__
    _ → fmap (appP (FOLFun folName [])) (mapM argTermToFOLTerm args)

predicateLogicalScheme ∷ [String] → Nat → Args → T FOLFormula
predicateLogicalScheme vars n args = do
  let var ∷ String
      var = vars !! fromIntegral n

  case length args of
    0 → __IMPOSSIBLE__
    _ → fmap (appP (FOLVar var)) (mapM argTermToFOLTerm args)

-- | Translate an Agda internal 'Term' to a first-order logic formula
-- 'FOLFormula'.
termToFormula ∷ Term → T FOLFormula
termToFormula term@(Def qName@(QName _ name) args) = do
  reportSLn "t2f" 10 $ "termToFormula Def:\n" ++ show term

  let cName ∷ C.Name
      cName = nameConcrete name

  case cName of
    C.NoName{} → __IMPOSSIBLE__

    C.Name _ [] → __IMPOSSIBLE__

    C.Name{} →
     case args of
       [] | isCNameFOLConst folTrue  → return TRUE

          | isCNameFOLConst folFalse → return FALSE

          | otherwise → do
            -- In this guard we translate 0-ary predicates,
            --
            -- e.g.  @P : Set@.
            folName ← qName2String qName
            return $ Predicate folName []

       (a : [])
         | isCNameFOLConstHoleRight folNot → fmap Not (argTermToFormula a)

         | isCNameFOLConst folExists ||
           isCNameFOLConst folForAll → do
             fm ← argTermToFormula a

             freshVar ← newTVar

             if isCNameFOLConst folExists
               then return $ Exists freshVar $ \_ → fm
               else return $ ForAll freshVar $ \_ → fm

         | otherwise → predicate qName args

       (a1 : a2 : [])
         | isCNameFOLConstTwoHoles folAnd → binConst And a1 a2

         | isCNameFOLConstTwoHoles folOr → binConst Or a1 a2

         | isCNameFOLConstTwoHoles folImplies → binConst Implies a1 a2

         | isCNameFOLConstTwoHoles folEquiv → binConst Equiv a1 a2

         | isCNameFOLConstTwoHoles folEquals → do
             reportSLn "t2f" 20 "Processing equals"
             liftM2 equal (argTermToFOLTerm a1) (argTermToFOLTerm a2)

         | otherwise → predicate qName args

       _ → predicate qName args

       where
       isCNameFOLConst ∷ String → Bool
       isCNameFOLConst constFOL =
         -- The equality on the data type @C.Name@ is defined to ignore
         -- ranges, so we use @noRange@.
         cName == C.Name noRange [C.Id constFOL]

       isCNameFOLConstHoleRight ∷ String → Bool
       isCNameFOLConstHoleRight constFOL =
         -- The operators are represented by a list with @Hole@'s.  See
         -- the documentation for @C.Name@.
         cName == C.Name noRange [C.Id constFOL, C.Hole]

       isCNameFOLConstTwoHoles ∷ String → Bool
       isCNameFOLConstTwoHoles constFOL =
         -- The operators are represented by a list with @Hole@'s.  See
         -- the documentation for @C.Name@.
         cName == C.Name noRange [C.Hole, C.Id constFOL, C.Hole]

termToFormula term@(Lam _ (Abs _ termLam)) = do
  reportSLn "t2f" 10 $ "termToFormula Lam:\n" ++ show term

  freshVar ← newTVar
  pushTVar freshVar
  f ← termToFormula termLam
  popTVar

  return f

termToFormula (Pi domTy (NoAbs x tyAbs)) = do
  reportSLn "t2f" 10 $
    "termToFormula Pi _ (NoAbs _ _):\n"
    ++ "domTy: " ++ show domTy ++ "\n"
    ++ "absTy: " ++ show (NoAbs x tyAbs)
  f2 ← typeToFormula tyAbs

  -- 27 June 2012. After the patch
  --
  -- Wed Sep 21 04:50:43 COT 2011  ulfn@chalmers.se
  --   * got rid of the Fun constructor in internal syntax (using Pi _ (NoAbs _ _) instead)
  --
  -- Agda is using (Pi _ (NoAbs _ _)) for the non-dependent
  -- functions. In a later patch, Agda changed somes (Pi _ (Abs _ _))
  -- to (Pi _ (NoAbs _ _)). The solution below works for *all* our cases.

  if x /= "_"
    then do
      case unDom domTy of
        -- The variable @x@ is an universal quantified variable not
        -- used, thefefore we generate a quantified first-order logic
        -- formula.
        El (Type (Max [])) (Def _ []) → do
          freshVar ← newTVar
          return $ ForAll freshVar (\_ → f2)

        -- The variable @x@ is a proof term, therefore we erase the
        -- quantication on it.
        El (Type (Max [])) (Def _ _) → do
          f1 ← domTypeToFormula domTy
          return $ Implies f1 f2

        _ → __IMPOSSIBLE__

    -- The variable @x@ is a proof term, therefore we erase the
    -- quantication on it.
    else do
      f1 ← domTypeToFormula domTy
      return $ Implies f1 f2

termToFormula (Pi domTy (Abs x tyAbs)) = do
  reportSLn "t2f" 10 $
    "termToFormula Pi _ (Abs _ _):\n"
    ++ "domTy: " ++ show domTy ++ "\n"
    ++ "absTy: " ++ show (Abs x tyAbs)

  freshVar ← newTVar

  reportSLn "t2f" 20 $
    "Starting processing in local environment with fresh variable "
    ++ show freshVar ++ " and type:\n" ++ show tyAbs

  pushTVar freshVar
  f ← typeToFormula tyAbs
  popTVar

  reportSLn "t2f" 20 $
    "Finalized processing in local environment with fresh variable "
    ++ show freshVar ++ " and type:\n" ++ show tyAbs

  reportSLn "t2f" 20 $ "The formula f is: " ++ show f

  case unDom domTy of
    -- The bounded variable is quantified on a @Set@,
    --
    -- e.g. the bounded variable is @d : D@ where @D : Set@,
    --
    -- so we can create a fresh variable and quantify on it without
    -- any problem.
    --
    -- N.B. the pattern matching on @(Def _ [])@.
    El (Type (Max [])) (Def _ []) → do
      reportSLn "t2f" 20 $
        "Adding universal quantification on variable " ++ show freshVar
      return $ ForAll freshVar (\_ → f)

    -- The bounded variable is quantified on a proof. Due to we have
    -- drop the quantification on proofs terms, this case is
    -- impossible.
    El (Type (Max [])) (Def _ _) → __IMPOSSIBLE__

    -- Non-FOL translation: First-order logic universal quantified
    -- functions term.
    --
    -- The bounded variable is quantified on a function of a @Set@ to
    -- a @Set@,
    --
    -- e.g. the bounded variable is @f : D → D@, where @D : Set@.
    --
    -- In this case we handle the bounded variable/function as a FOL
    -- variable in @termToFOLTerm (Var n args)@, which is processed
    -- first due to lazyness. We quantified on this variable.
    El (Type (Max []))
       (Pi (Dom _ _ (El (Type (Max [])) (Def _ [])))
           (NoAbs _ (El (Type (Max [])) (Def _ [])))) → do
      reportSLn "t2f" 20
        "Removing a quantification on a function of a Set to a Set"
      return $ ForAll freshVar (\_ → f)

    -- N.B. The next case is just a generalization to various
    -- arguments of the previous case.

    -- Non-FOL translation: First-order logic universal quantified
    -- functions term.
    --
    -- The bounded variable is quantified on a function of a @Set@ to
    -- a @Set@,
    --
    -- e.g. the bounded variable is @f : D → D → D@, where @D : Set@.
    --
    -- In this case we handle the bounded variable/function as a FOL
    -- variable in @termToFOLTerm (Var n args)@, which is processed
    -- first due to lazyness. We quantified on this variable.
    El (Type (Max []))
       (Pi (Dom _ _ (El (Type (Max [])) (Def _ [])))
           (NoAbs _ (El (Type (Max [])) (Pi _ (NoAbs _ _))))) → do
      reportSLn "t2f" 20
        "Removing a quantification on a function of a Set to a Set"
      -- 31 May 2012. We don't have an example of this case.
      --
      -- return $ ForAll freshVar (\_ → f)
      __IMPOSSIBLE__

    El (Type (Max [])) someTerm → do
      reportSLn "t2f" 20 $ "The term someterm is: " ++ show someTerm
      __IMPOSSIBLE__

    -- Non-FOL translation: First-order logic universal quantified
    -- formulae.
    --
    -- The bounded variable is quantified on a @Set₁@,
    --
    -- e.g. the bounded variable is @P : Set@,
    --
    -- so we just return the consequent. We use this case for translate
    -- predicate logical schemata such
    --
    -- @∨-comm  : {P Q : Set} → P ∨ Q → Q ∨ P@.
    --
    -- In this case we handle the bounded variable/function in
    -- @termToFormula (Var n args)@, which is processed first due to
    -- lazyness.

    El (Type (Max [ClosedLevel 1])) (Sort _) → do
      reportSLn "t2f" 20 $ "The type domTy is: " ++ show domTy

      unlessM (getTOpt optNonFOLFormula) $
        throwError $ "The translation of first-order logic universal"
                     ++ " quantified formulae is disable by default."
                     ++ " Use option --non-fol-formula"
      return f

    -- Non-FOL translation: First-order logic universal quantified
    -- propositional functions.
    --
    -- The bounded variable is quantified on a @Set₁@,
    --
    -- e.g. the bounded variable is @P : D → D → Set@.
    --
    -- In this case we return a forall bind on the fresh variable. We
    -- use this case for translate predicate logic schemas, e.g.
    --
    --   ∨-comm₂ : {P₂ Q₂ : D → D → Set}{x y : D} →
    --             P₂ x y ∨ Q₂ x y → Q₂ x y ∨ P₂ x y

    El (Type (Max [ClosedLevel 1])) (Pi _ (NoAbs _ _)) →
      return $ ForAll freshVar (\_ → f)

    -- Other cases
    El (Type (Max [ClosedLevel 1])) (Def _ _)        → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (DontCare _)     → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Con _ _)        → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Lam _ _)        → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Level _)        → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Lit _)          → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (MetaV _ _)      → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Pi _ (Abs _ _)) → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Var _ _)        → __IMPOSSIBLE__

    someType → do
      reportSLn "t2f" 20 $ "The type domTy is: " ++ show someType
      __IMPOSSIBLE__

termToFormula term@(Var n args) = do
  reportSLn "t2f" 10 $ "termToFormula Var: " ++ show term

  vars ← getTVars

  when (length vars <= fromIntegral n) (__IMPOSSIBLE__)

  case args of
    -- N.B. In this case we *don't* use the Koen's approach.
    [] → return $ Predicate (vars !! fromIntegral n) []

    -- Non-FOL translation: First-order logic universal quantified
    -- propositional functions.

    -- If we have a bounded variable quantified on a function of a
    -- @Set@ to a @Set₁@, for example, the variable/predicate @P@ in
    --
    -- @(P : D → Set) → (x : D) → P x → P x@
    --
    -- we are quantifying on this variable/function
    --
    -- (see @termToFormula (Pi domTy (Abs _ tyAbs))@),
    --
    -- therefore we need to apply this variable/predicate to the
    -- others variables. See an example in
    -- Test.Succeed.AgdaInternalTerms.Var1.agda.
    _ → do
      unlessM (getTOpt optNonFOLPropositionalFunction) $
        throwError $ "The translation of first-order logic universal"
                     ++ " quantified function terms is disable by default."
                     ++ " Use option --non-fol-propositional-function"

      predicateLogicalScheme vars n args

termToFormula (DontCare _)        = __IMPOSSIBLE__
termToFormula (Con _ _)           = __IMPOSSIBLE__
termToFormula (Lam _ (NoAbs _ _)) = __IMPOSSIBLE__
termToFormula (Level _)           = __IMPOSSIBLE__
termToFormula (Lit _)             = __IMPOSSIBLE__
termToFormula (MetaV _ _)         = __IMPOSSIBLE__
termToFormula (Sort _)            = __IMPOSSIBLE__

-- Translate the function @foo x1 ... xn@ to
--
-- @kAppFn (... kAppFn(kAppFn(foo, x1), x2), ..., xn)@.
appArgsFn ∷ String → Args → T FOLTerm
appArgsFn fn args = do
  termsFOL ← mapM argTermToFOLTerm args
  return $ foldl' appFn (FOLFun fn []) termsFOL

-- | Translate an Agda internal 'Term' to a first-order logic term
-- 'FOLTerm'.
termToFOLTerm ∷ Term → T FOLTerm

termToFOLTerm term@(Con (QName _ name) args) = do
  reportSLn "t2t" 10 $ "termToFOLTerm Con:\n" ++ show term

  let cName ∷ C.Name
      cName = nameConcrete name

  case cName of
    C.NoName{}  → __IMPOSSIBLE__

    C.Name _ [] → __IMPOSSIBLE__

    -- The term @Con@ doesn't have holes. It should be translated as a
    -- first-order logic function.
    C.Name _ [C.Id str] →
     case args of
       [] → return $ FOLFun str []
       _  → appArgsFn str args

    -- The term @Con@ has holes. It is translated as a first-order
    -- logic function.
    C.Name _ _ → __IMPOSSIBLE__
    -- 2012-04-22: We do not have an example of it.
    -- C.Name _ parts →
    --   case args of
    --     [] → __IMPOSSIBLE__
    --     _  → appArgsFn (concatName parts) args

termToFOLTerm term@(Def (QName _ name) args) = do
  reportSLn "t2t" 10 $ "termToFOLTerm Def:\n" ++ show term

  let cName ∷ C.Name
      cName = nameConcrete name

  case cName of
    C.NoName{}  → __IMPOSSIBLE__

    C.Name _ [] → __IMPOSSIBLE__

    -- The term @Def@ doesn't have holes. It is translated as a
    -- first-order logic function.
    C.Name _ [C.Id str] →
     case args of
       [] → return $ FOLFun str []
       _  → appArgsFn str args

    -- The term @Def@ has holes. It is translated as a first-order
    -- logic function.
    C.Name _ parts →
      case args of
        [] → __IMPOSSIBLE__
        _  → appArgsFn (concatName parts) args

termToFOLTerm term@(Var n args) = do
  reportSLn "t2t" 10 $ "termToFOLTerm Var:\n" ++ show term

  vars ← getTVars

  when (length vars <= fromIntegral n) (__IMPOSSIBLE__)

  case args of
    [] → return $ FOLVar (vars !! fromIntegral n)

    -- Non-FOL translation: First-order logic universal quantified
    -- functions term.

    -- If we have a bounded variable quantified on a function of a Set
    -- to a Set, for example, the variable/function @f@ in
    --
    -- @(f : D → D) → (a : D) → (lam f) ∙ a ≡ f a@
    --
    -- we are quantifying on this variable/function
    --
    -- (see @termToFormula (Pi domTy (Abs _ tyAbs))@),
    --
    -- therefore we need to apply this variable/function to the others
    -- variables. See an example in
    -- Test.Succeed.AgdaInternalTerms.Var2.agda
    varArgs → do
      unlessM (getTOpt optNonFOLFunction) $
        throwError $ "The translation of first-order logic universal"
                     ++ " quantified function terms is disable by default."
                     ++ " Use option --non-fol-function"

      termsFOL ← mapM argTermToFOLTerm varArgs
      return $ foldl' appFn (FOLVar (vars !! fromIntegral n)) termsFOL

termToFOLTerm (DontCare _) = __IMPOSSIBLE__
termToFOLTerm (Lam _ _)    = __IMPOSSIBLE__
termToFOLTerm (Level _)    = __IMPOSSIBLE__
termToFOLTerm (Lit _)      = __IMPOSSIBLE__
termToFOLTerm (MetaV _ _)  = __IMPOSSIBLE__
termToFOLTerm (Pi _ _)     = __IMPOSSIBLE__
termToFOLTerm (Sort _)     = __IMPOSSIBLE__
