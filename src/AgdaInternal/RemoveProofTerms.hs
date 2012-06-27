------------------------------------------------------------------------------
-- |
-- Module      : AgdaInternal.RemoveProofTerms
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Remove references to variables which are proof terms from Agda
-- internal types.

------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

------------------------------------------------------------------------------
-- General description
-- Example (Test.Succeed.Conjectures.DefinitionsInsideWhereClauses)

-- +-rightIdentity : ∀ {n} → N n → n + zero ≡ n
-- +-rightIdentity Nn = indN P P0 iStep Nn
--   where
--     P : D → Set
--     P i = i + zero ≡ i
--     {-# ATP definition P #-}

--     postulate
--       P0 : P zero
--     {-# ATP prove P0 #-}

--     postulate
--       iStep : ∀ {i} → N i → P i → P (succ i)
--     {-# ATP prove iStep #-}

-- The Agda internal type of P0 is

-- El (Type (Max []))
--    (Pi r{El (Type (Max [])) (Def Test.Succeed.Conjectures.DefinitionsInsideWhereClauses.D [])}
--        (Abs ".n" El (Type (Max []))
--                     (Pi r(El (Type (Max [])) (Def Test.Succeed.Conjectures.DefinitionsInsideWhereClauses.N [r(Var 0 [])]))
--                         (Abs "Nn" El (Type (Max []))
--                                      (Def Test.Succeed.Conjectures.DefinitionsInsideWhereClauses._.P [r{Var 1 []},r(Var 0 []),r(Def Test.Succeed.Conjectures.DefinitionsInsideWhereClauses.zero [])])))))

-- The variable Nn is a proof term (i.e. Nn : N n) and it is referenced in

-- Def Test.Succeed.Conjectures.DefinitionsInsideWhereClauses._.P [r{Var 1 []},r(Var 0 [])...       (1)

-- using its de Brujin name, i.e. r(Var 0 []). After remove this
-- reference the internal term (1) is converted to

-- Test.Succeed.Conjectures.DefinitionsInsideWhereClauses._.P [r{Var 1 []}...].

-- In addition the quantification on Nn will be removed too. See
-- FOL.Translation.Internal.Terms.termToFormula (on Pi terms).

-- End general description.

------------------------------------------------------------------------------
module AgdaInternal.RemoveProofTerms
  ( removeProofTerm
  , BoundedVarsType(boundedVarsType)
  ) where

------------------------------------------------------------------------------
-- Haskell imports

import Control.Monad       ( liftM2, when )
import Control.Monad.Error ( MonadError(throwError) )

import Data.List ( elemIndex )

------------------------------------------------------------------------------
-- Agda libray imports

import Agda.Syntax.Common ( Arg(Arg), Dom(Dom), Nat )

import Agda.Syntax.Internal
  ( Abs(Abs, NoAbs)
  , Args
  , Level(Max)
  , PlusLevel(ClosedLevel)
  , Term(Con, Def, DontCare, Lam, Level, Lit, MetaV, Pi, Sort, Var)
  , Sort(Type)
  , Type(El)
  , var
  )

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

import Monad.Base    ( getTVars, popTVar, pushTVar, T )
import Monad.Reports ( reportSLn )
import Utils.Show    ( showLn )

#include "../undefined.h"

------------------------------------------------------------------------------
-- We only need to remove the variables which are proof terms, so we
-- collect the types of the bounded variables using the type class
-- BoundedVarsType. The de Bruijn indexes are assigned from right to
-- left,
--
-- e.g.  in @(A B C : Set) → ...@, @A@ is 2, @B@ is 1, and @C@ is 0,
--
-- so we need create the list in the same order.

-- | Types of the bounded variables in an Agda entity.
class BoundedVarsType a where
  boundedVarsType ∷ a → [(String, Type)]

instance BoundedVarsType Type where
  boundedVarsType (El (Type _) term) = boundedVarsType term
  boundedVarsType _                  = __IMPOSSIBLE__

instance BoundedVarsType Term where
  -- TODO: In Lam terms we bound variables, but they seem doesn't have
  -- associated types. Therefore, we associate a "DontCare" type.
  --
  -- boundedVarsType (Lam _ (Abs x absTerm)) =
  --   boundedVarsType absTerm ++ [(x, El (Type (Max [])) DontCare)]

  -- We only have real bounded variables in Pi _ (Abs _ _) terms.
  boundedVarsType (Pi _ (NoAbs _ absTy)) = boundedVarsType absTy
  boundedVarsType (Pi (Dom _ _ ty) (Abs x absTy)) = (x, ty) : boundedVarsType absTy

  boundedVarsType (Def _ args) = boundedVarsType args

  boundedVarsType (Con _ _) = []
  boundedVarsType (Lam _ _) = []
  boundedVarsType (Var _ _) = []

  boundedVarsType (DontCare _) = __IMPOSSIBLE__
  boundedVarsType (Level _)    = __IMPOSSIBLE__
  boundedVarsType (Lit _)      = __IMPOSSIBLE__
  boundedVarsType (MetaV _ _)  = __IMPOSSIBLE__
  boundedVarsType (Sort _)     = __IMPOSSIBLE__

instance BoundedVarsType a ⇒ BoundedVarsType (Arg a) where
  boundedVarsType (Arg _ _ e) = boundedVarsType e

instance BoundedVarsType a ⇒ BoundedVarsType [a] where
  boundedVarsType = concatMap boundedVarsType

-- | Remove the reference to a variable (i.e. Var n args) in an Agda
-- entity.
class DropVar a where
  removeVar ∷ a → String → T a

instance DropVar Type where
  removeVar (El ty@(Type _) term) x = fmap (El ty) (removeVar term x)
  removeVar _                     _ = __IMPOSSIBLE__

instance DropVar Term where
  removeVar (Def qname args) x = fmap (Def qname) (removeVar args x)

  removeVar (Lam h (Abs y absTerm)) x = do
    pushTVar y

    reportSLn "removeVar" 20 $ "Pushed variable " ++ show y

    auxTerm ← removeVar absTerm x

    popTVar

    reportSLn "removePT" 20 $ "Pop variable " ++ show y

    return $ Lam h (Abs y auxTerm)

  -- N.B. The variables *are* removed from the (Arg Type).
  removeVar (Pi domTy (NoAbs y absTy)) x = do
    newArgTy ← removeVar domTy x
    newAbsTy ← removeVar absTy x
    return $ Pi newArgTy (NoAbs y newAbsTy)

  -- N.B. The variables *are not* removed from the (Arg Type), they
  -- are only removed from the (Abs Type).
  removeVar (Pi domTy (Abs y absTy)) x = do

    pushTVar y
    reportSLn "removeVar" 20 $ "Pushed variable " ++ show y

    -- If the Pi term is on a proof term, we replace it by a Pi term
    -- which is not a proof term.
    newTerm ← if y /= x
                then do
                  newType ← removeVar absTy x
                  return $ Pi domTy (Abs y newType)
                else do
                  newType ← removeVar absTy x
                  -- We use "_" because Agda uses it.
                  return $ Pi domTy (NoAbs "_" newType)

    popTVar
    reportSLn "removePT" 20 $ "Pop variable " ++ show y
    return newTerm

  removeVar (Con _ _)           _ = __IMPOSSIBLE__
  removeVar (DontCare _)        _ = __IMPOSSIBLE__
  removeVar (Lam _ (NoAbs _ _)) _ = __IMPOSSIBLE__
  removeVar (Level _)           _ = __IMPOSSIBLE__
  removeVar (Lit _)             _ = __IMPOSSIBLE__
  removeVar (MetaV _ _)         _ = __IMPOSSIBLE__
  removeVar (Sort _)            _ = __IMPOSSIBLE__
  removeVar (Var _ _)           _ = __IMPOSSIBLE__

instance DropVar a ⇒ DropVar (Dom a) where
  removeVar (Dom h r e) x = fmap (Dom h r) (removeVar e x)

-- In the Agda source code (Agda.Syntax.Internal) we have
--
-- type Args = [Arg Term]
--
-- however, we cannot create the instance of Args based on a map,
-- because in some cases we need to erase the term.

-- Requires @TypeSynonymInstances@ and @FlexibleInstances@.
instance DropVar Args where
  removeVar [] _ = return []

  removeVar (Arg h r term@(Var n []) : args) x = do
    vars ← getTVars

    when (x == "_") $
      throwError "The translation of underscore variables is not implemented"

    let index ∷ Nat
        index = case elemIndex x vars of
                  Nothing →  __IMPOSSIBLE__
                  Just i  → fromIntegral i

    if n == index
      then removeVar args x
      else if n < index
             then fmap ((:) (Arg h r term)) (removeVar args x)
             else fmap ((:) (Arg h r (var (n - 1)))) (removeVar args x)

  removeVar (Arg _ _ (Var _ _) : _) _ = __IMPOSSIBLE__

  removeVar (Arg h r term : args) x =
    liftM2 (\t ts → Arg h r t : ts) (removeVar term x) (removeVar args x)

-- | Remove a proof term from an Agda 'Type'.
removeProofTerm ∷ Type → (String, Type) → T Type
removeProofTerm ty (x, typeVar) = do
  reportSLn "removePT" 20 $
    "It is necessary to remove the variable " ++ show x ++ "?"

  case typeVar of
    -- The variable's type is a @Set@,
    --
    -- e.g. the variable is @d : D@, where @D : Set@
    --
    -- so we don't do anything.

    -- N.B. the pattern matching on @(Def _ [])@.
    El (Type (Max [])) (Def _ []) → return ty

    -- The variable's type is a proof,
    --
    -- e.g. the variable is @Nn : N n@ where @D : Set@, @n : D@ and @N
    -- : D → Set@.
    --
    -- In this case, we remove the reference to this
    -- variable.

    -- N.B. the pattern matching on @(Def _ _)@.

    El (Type (Max [])) (Def _ _) → removeVar ty x

    -- The variable's type is a function type, i.e. @Pi _ (NoAbs _ _ )@
    --
    -- e.g. the variable is @f : D → D@, where @D : Set@.

    -- -- In the class TypesOfVar we associated to the variables bounded
    -- -- in Lam terms the type DontCare.
    -- El (Type (Max [])) DontCare → return ty

    -- Because the variable is not a proof term we don't do anything.
    El (Type (Max []))
       (Pi (Dom _ _ (El (Type (Max [])) (Def _ [])))
           (NoAbs _ (El (Type (Max [])) (Def _ [])))) → return ty

    -- The next case is just a generalization to various arguments of
    -- the previous case.

    -- The variable's type is a function type,
    --
    -- e.g. the variable is @f : D → D → D@, where @D : Set@.

    -- Because the variable is not a proof term we don't do anything.
    El (Type (Max []))
       (Pi (Dom _ _ (El (Type (Max [])) (Def _ [])))
           (NoAbs _ (El (Type (Max [])) (Pi _ (NoAbs _ _))))) →
       __IMPOSSIBLE__ -- return ty

    -- We don't erase these proofs terms.
    El (Type (Max [])) someTerm → do
      reportSLn "removePT" 20 $
                "The term someTerm is: " ++ show someTerm
      throwError $ "It is necessary to erase the proof term\n"
                   ++ showLn someTerm
                   ++ "but we do not know how to do it"

    -- The variable's type is @Set₁@,
    --
    -- e.g. the variable is @P : Set@.
    --
    -- Because the variable is not a proof term we don't do anything.
    El (Type (Max [ClosedLevel 1])) (Sort _) → return ty

    -- N.B. The next case is just a generalization to various
    -- arguments of the previous case.

    -- The variable's type is @Set₁@,
    --
    -- e.g. the variable is @P : D → Set@.
    --
    -- Because the variable is not a proof term we don't do anything.
    El (Type (Max [ClosedLevel 1])) (Pi _ (NoAbs _ _)) → return ty

    -- Other cases
    El (Type (Max [ClosedLevel 1])) (Def _ _)        → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (DontCare _)     → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Con _ _)        → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Lam _ _)        → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (MetaV _ _)      → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Pi _ (Abs _ _)) → __IMPOSSIBLE__
    El (Type (Max [ClosedLevel 1])) (Var _ _)        → __IMPOSSIBLE__

    someType → do
      reportSLn "removePT" 20 $
                "The type varType is: " ++ show someType
      __IMPOSSIBLE__
