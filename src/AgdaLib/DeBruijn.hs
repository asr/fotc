------------------------------------------------------------------------------
-- |
-- Module      : AgdaLib.Syntax.DeBruijn
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2012
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <andres.sicard.ramirez@gmail.com>
-- Stability   : experimental
--
-- Functions on de Bruijn indexes.
------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

-- There are various cases (e.g. eta-expansion, translation of
-- symbols' definitions, elimination of quantification on variables
-- which are proof terms) where it is necessary modify the variables
-- in the Agda internal terms, i.e. it is necessary to modify the
-- Bruijn index in the variable.

module AgdaLib.DeBruijn
  ( ChangeIndex(changeIndex)
  , DecIndex(decIndex)
  , dropProofTerm
  , IncIndex(incIndex)
  , TypesOfVars(typesOfVars)
  , varToIndex
  ) where

------------------------------------------------------------------------------
-- Haskell imports

#if __GLASGOW_HASKELL__ == 612
import Control.Monad ( Monad((>>), (>>=), fail) )
#endif
import Control.Monad ( liftM2, Monad(return), when )

import Control.Monad.Error ( MonadError(throwError) )

#if __GLASGOW_HASKELL__ < 702
import Data.Char ( String )
#else
import Data.String ( String )
#endif

import Data.Eq       ( Eq((==), (/=)) )
import Data.Function ( ($) )
import Data.Functor  ( fmap )
import Data.List     ( (++), elemIndex, map )
import Data.Maybe    ( Maybe(Just, Nothing) )
import Data.Ord      ( Ord((<), (>)) )

#if __GLASGOW_HASKELL__ == 612
import GHC.Num ( Num(fromInteger) )
#endif
import GHC.Num  ( Num((+), (-)) )
import GHC.Real ( fromIntegral )

import Text.Show ( Show(show) )

------------------------------------------------------------------------------
-- Agda libray imports

import Agda.Syntax.Common ( Arg(Arg), Dom(Dom), Nat )

import Agda.Syntax.Internal
  ( Abs(Abs, NoAbs)
  , Args
  , ClauseBody(Bind,Body)
  , Level(Max)
  , PlusLevel(ClosedLevel)
  , Tele(EmptyTel, ExtendTel)
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
-- | To increase by one the de Bruijn index of the variable.
class IncIndex a where
  incIndex ∷ a → a

instance IncIndex Term where
  incIndex (Var n [])  = var (n + 1)
  incIndex (Var _ _)   = __IMPOSSIBLE__

  incIndex (Con _ _)    = __IMPOSSIBLE__
  incIndex (Def _ _)    = __IMPOSSIBLE__
  incIndex (DontCare _) = __IMPOSSIBLE__
  incIndex (Lam _ _)    = __IMPOSSIBLE__
  incIndex (Level _)    = __IMPOSSIBLE__
  incIndex (Lit _)      = __IMPOSSIBLE__
  incIndex (MetaV _ _)  = __IMPOSSIBLE__
  incIndex (Pi _ _)     = __IMPOSSIBLE__
  incIndex (Sort _)     = __IMPOSSIBLE__

-- Requires FlexibleInstances.
instance IncIndex (Arg Term) where
  incIndex (Arg h r term) = Arg h r $ incIndex term

------------------------------------------------------------------------------
-- | To decrease by one the de Bruijn index of the variable.
class DecIndex a where
  decIndex ∷ a → a

instance DecIndex Term where
  decIndex (Def qname args) = Def qname $ decIndex args

  decIndex (Var 0 [])  = __IMPOSSIBLE__
  decIndex (Var n [])  = var (n - 1)
  decIndex (Var _ _)   = __IMPOSSIBLE__

  decIndex (Con _ _)    = __IMPOSSIBLE__
  decIndex (DontCare _) = __IMPOSSIBLE__
  decIndex (Lam _ _)    = __IMPOSSIBLE__
  decIndex (Level _)    = __IMPOSSIBLE__
  decIndex (Lit _)      = __IMPOSSIBLE__
  decIndex (MetaV _ _)  = __IMPOSSIBLE__
  decIndex (Pi _ _)     = __IMPOSSIBLE__
  decIndex (Sort _)     = __IMPOSSIBLE__

instance DecIndex a ⇒ DecIndex [a] where
  decIndex = map decIndex

instance DecIndex Type where
  decIndex (El (Type (Max [])) term) = El (Type (Max [])) (decIndex term)
  decIndex _                         = __IMPOSSIBLE__

instance DecIndex a ⇒ DecIndex (Arg a) where
  decIndex (Arg h r a) = Arg h r $ decIndex a

instance DecIndex a ⇒ DecIndex (Dom a) where
  decIndex (Dom h r a) = Dom h r $ decIndex a

instance DecIndex a ⇒ DecIndex (Abs a) where
  decIndex (Abs name body) = Abs name $ decIndex body
  decIndex (NoAbs _ _)     = __IMPOSSIBLE__

instance DecIndex a ⇒ DecIndex (Tele a) where
  decIndex EmptyTel          = EmptyTel
  decIndex (ExtendTel a tel) = ExtendTel (decIndex a) (decIndex tel)

------------------------------------------------------------------------------
-- We collect the variables' names using the type class VarNames. The
-- de Bruijn indexes are assigned from right to left,
--
-- e.g.  in '(A B C : Set) → ...', A is 2, B is 1, and C is 0,
--
-- so we need create the list in the same order.

class VarNames a where
  varNames ∷ a → [String]

instance VarNames Term where
  varNames (Def _ args) = varNames args

  varNames (Lam _ (Abs x term)) = varNames term ++ [x]

  varNames (Var _ [])   = []
  varNames (Var _ args) = varNames args

  varNames (Con _ _)           = __IMPOSSIBLE__
  varNames (DontCare _)        = __IMPOSSIBLE__
  varNames (Lam _ (NoAbs _ _)) = __IMPOSSIBLE__
  varNames (Level _)           = __IMPOSSIBLE__
  varNames (Lit _)             = __IMPOSSIBLE__
  varNames (MetaV _ _)         = __IMPOSSIBLE__
  varNames (Pi _ _)            = __IMPOSSIBLE__
  varNames (Sort _)            = __IMPOSSIBLE__

instance VarNames (Arg Term) where
  varNames (Arg _ _ term) = varNames term

instance VarNames Args where
  varNames []           = []
  varNames (arg : args) = varNames arg ++ varNames args

instance VarNames ClauseBody where
  varNames (Bind (Abs x cBody)) = varNames cBody ++ [x]
  varNames (Body term)          = varNames term
  varNames _                    = __IMPOSSIBLE__

-- Return the de Bruijn index of a variable in a ClauseBody.
varToIndex ∷ ClauseBody → String → Nat
varToIndex cBody x =
  case elemIndex x (varNames cBody) of
    Just n  → fromIntegral n
    Nothing → __IMPOSSIBLE__

------------------------------------------------------------------------------
-- To change a de Bruijn index with respect to other index.
-- Let's suppose we have something like

-- λ m : D → (λ n : D → (λ Nn : N n → (λ h : D → ... Var 2 ...)))

-- where 'Var 2' is the de Bruijn index of the variable n. If we
-- drop the quantification on the proof term Nn

-- λ m : D → (λ n : D → (λ h : D → ...))

-- we need change 'Var 2' by 'Var 1'.

class ChangeIndex a where
  changeIndex ∷ a → Nat → a

instance ChangeIndex Term where
  changeIndex term@(Def _ []) _ = term

  changeIndex (Def qName args) index = Def qName $ changeIndex args index

  changeIndex (Lam h (Abs x term)) index = Lam h (Abs x (changeIndex term index))

  -- When the variable is part of an argument, it was processed in the
  -- Args instance.
  changeIndex term@(Var n []) index
    -- The variable was before than the quantified variable, we don't
    -- do nothing.
    | n < index = term

    -- The variable was after than the quantified variable, we need
    -- "unbound" the quantified variable.
    | n > index = var (n - 1)

    | n == index = __IMPOSSIBLE__

  changeIndex (Con _ _)           _ = __IMPOSSIBLE__
  changeIndex (DontCare _)        _ = __IMPOSSIBLE__
  changeIndex (Lam _ (NoAbs _ _)) _ = __IMPOSSIBLE__
  changeIndex (Level _)           _ = __IMPOSSIBLE__
  changeIndex (Lit _)             _ = __IMPOSSIBLE__
  changeIndex (MetaV _ _)         _ = __IMPOSSIBLE__
  changeIndex (Pi _ _)            _ = __IMPOSSIBLE__
  changeIndex (Sort _)            _ = __IMPOSSIBLE__
  changeIndex (Var _ _)           _ = __IMPOSSIBLE__

-- In the Agda source code (Agda.Syntax.Internal) we have
--
-- type Args = [Arg Term]
--
-- however, we cannot create the instance of Args based on a simple
-- map, because in some cases we need to erase the term.

instance ChangeIndex Args where
  changeIndex [] _ = []

  changeIndex (Arg h r term@(Var n []) : args) index
    -- The variable was before than the quantified variable, we don't
    -- do nothing.
    | n < index = Arg h r term : changeIndex args index

    -- The variable was after than the quantified variable, we need
    -- "unbound" the quantified variable.
    | n > index = Arg h r (var (n - 1)) : changeIndex args index

    -- The variable is the quantified variable. This can happen when
    -- the quantified variable is used indirectly by other term via
    -- for example a where clause (see for example xxx). In this case,
    -- we drop the variable. Before this modification, we returned
    -- __IMPOSSIBLE__.
    | n == index = changeIndex args index

  changeIndex (Arg _ _ (Var _ _) : _) _ = __IMPOSSIBLE__

  changeIndex (Arg h r term : args) index = Arg h r (changeIndex term index) :
                                            changeIndex args index

instance ChangeIndex ClauseBody where
  changeIndex (Bind (Abs x cBody)) index = Bind (Abs x (changeIndex cBody index))
  changeIndex (Body term)          index = Body $ changeIndex term index
  changeIndex _                    _     = __IMPOSSIBLE__

------------------------------------------------------------------------------
-- Remove references to variables which are proof terms from
-- the Agda internal types.

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

-- using its de Brujin name, i.e. r(Var 0 []). After drop this
-- reference the internal term (1) is converted to

-- Test.Succeed.Conjectures.DefinitionsInsideWhereClauses._.P [r{Var 1 []}...].

-- In addition the quantification on Nn will be dropped too. See
-- FOL.Translation.Internal.Terms.termToFormula (on Pi terms).

-- End general description.
------------------------------------------------------------------------------

-- We only need to drop the variables which are proof terms, so we
-- collect the types of the variables using the type class
-- TypesOfVars. The de Bruijn indexes are assigned from right to left,
--
-- e.g.  in '(A B C : Set) → ...', A is 2, B is 1, and C is 0,
--
-- so we need create the list in the same order.

class TypesOfVars a where
  typesOfVars ∷ a → [(String, Type)]

instance TypesOfVars Type where
  typesOfVars (El (Type _) term) = typesOfVars term
  typesOfVars _                  = __IMPOSSIBLE__

instance TypesOfVars Term where
  -- TODO: In Lam terms we bound variables, but they seem doesn't have
  -- associated types. Therefore, we associate a "DontCare" type.
  --
  -- typesOfVars (Lam _ (Abs x absTerm)) =
  --   typesOfVars absTerm ++ [(x, El (Type (Max [])) DontCare)]

  -- We only have real bounded variables in Pi _ (Abs _ _) terms.
  typesOfVars (Pi _            (NoAbs _ absTy)) = typesOfVars absTy
  typesOfVars (Pi (Dom _ _ ty) (Abs x absTy))   = (x, ty) : typesOfVars absTy

  typesOfVars (Def _ args) = typesOfVars args

  typesOfVars (Con _ _)                    = []
  typesOfVars (DontCare _)                 = []
  typesOfVars (Lam _ _)                    = []
  typesOfVars (Level _)                    = []
  typesOfVars (Lit _)                      = []
  typesOfVars (MetaV _ _)                  = []
  typesOfVars (Sort _)                     = []
  typesOfVars (Var _ _)                    = []

instance TypesOfVars (Arg Term) where
  typesOfVars (Arg _ _ term) = typesOfVars term

instance TypesOfVars Args where
  typesOfVars []       = []
  typesOfVars (x : xs) = typesOfVars x ++ typesOfVars xs

-- instance TypesOfVars (Abs Type) where
--   typesOfVars (Abs _ ty) = typesOfVars ty

-- | Remove the reference to a variable (i.e. Var n args) from an Agda
-- internal entity.
class DropVar a where
  dropVar ∷ a → String → T a

instance DropVar Type where
  dropVar (El ty@(Type _) term) x = fmap (El ty) (dropVar term x)
  dropVar _                     _ = __IMPOSSIBLE__

instance DropVar Term where
  dropVar (Def qname args) x = fmap (Def qname) (dropVar args x)

  dropVar (Lam h (Abs y absTerm)) x = do
    pushTVar y

    reportSLn "dropVar" 20 $ "Pushed variable: " ++ y

    auxTerm ← dropVar absTerm x

    popTVar

    reportSLn "dropPT" 20 $ "Pop variable: " ++ y

    return $ Lam h (Abs y auxTerm)

  -- N.B. The variables *are* dropped from the (Arg Type).
  dropVar (Pi domTy (NoAbs y absTy)) x = do
    newArgTy ← dropVar domTy x
    newAbsTy ← dropVar absTy x
    return $ Pi newArgTy (NoAbs y newAbsTy)

  -- N.B. The variables *are not* dropped from the (Arg Type), they
  -- are only dropped from the (Abs Type).
  dropVar (Pi domTy (Abs y absTy)) x = do

    pushTVar y
    reportSLn "dropVar" 20 $ "Pushed variable: " ++ y

    -- If the Pi term is on a proof term, we replace it by a Pi term
    -- which is not a proof term.
    newTerm ← if y /= x
                then do
                  newType ← dropVar absTy x
                  return $ Pi domTy (Abs y newType)
                else do
                  newType ← dropVar absTy x
                  -- We use "_" because Agda uses it.
                  return $ Pi domTy (NoAbs "_" newType)

    popTVar
    reportSLn "dropPT" 20 $ "Pop variable: " ++ y
    return newTerm

  dropVar (Con _ _)           _ = __IMPOSSIBLE__
  dropVar (DontCare _)        _ = __IMPOSSIBLE__
  dropVar (Lam _ (NoAbs _ _)) _ = __IMPOSSIBLE__
  dropVar (Level _)           _ = __IMPOSSIBLE__
  dropVar (Lit _)             _ = __IMPOSSIBLE__
  dropVar (MetaV _ _)         _ = __IMPOSSIBLE__
  dropVar (Sort _)            _ = __IMPOSSIBLE__
  dropVar (Var _ _)           _ = __IMPOSSIBLE__

instance DropVar (Arg Type) where
  dropVar (Arg h r ty) x = fmap (Arg h r) (dropVar ty x)

instance DropVar (Dom Type) where
  dropVar (Dom h r ty) x = fmap (Dom h r) (dropVar ty x)

-- In the Agda source code (Agda.Syntax.Internal) we have
--
-- type Args = [Arg Term]
--
-- however, we cannot create the instance of Args based on a map,
-- because in some cases we need to erase the term.

-- Requires TypeSynonymInstances.
instance DropVar Args where
  dropVar [] _ = return []

  dropVar (Arg h r term@(Var n []) : args) x = do
    vars ← getTVars

    when (x == "_") $
      throwError "The translation of underscore variables is not implemented"

    let index ∷ Nat
        index = case elemIndex x vars of
                  Nothing →  __IMPOSSIBLE__
                  Just i  → fromIntegral i

    if n == index
      then dropVar args x
      else if n < index
             then fmap ((:) (Arg h r term)) (dropVar args x)
             else fmap ((:) (Arg h r (var (n - 1)))) (dropVar args x)

  dropVar (Arg _ _ (Var _ _) : _) _ = __IMPOSSIBLE__

  dropVar (Arg h r term : args) x =
    liftM2 (\t ts → Arg h r t : ts) (dropVar term x) (dropVar args x)

dropProofTerm ∷ Type → (String, Type) → T Type
dropProofTerm ty (x, typeVar) = do
  reportSLn "dropPT" 20 $ "Dropping variable: " ++ x

  case typeVar of
    -- The variable's type is a Set,
    --
    -- e.g. the variable is d : D, where D : Set
    --
    -- so we don't do anything.

    -- N.B. the pattern matching on (Def _ []).
    El (Type (Max [])) (Def _ []) → return ty

    -- The variable's type is a proof,
    --
    -- e.g. the variable is 'Nn : N n' where D : Set, n : D and N :
    -- D → Set.
    --
    -- In this case, we drop the reference to this
    -- variable.

    -- N.B. the pattern matching on (Def _ _).

    El (Type (Max [])) (Def _ _) → dropVar ty x

    -- The variable's type is a function type, i.e. Pi _ (NoAbs _ _ )
    --
    -- e.g. the variable is f : D → D, where D : Set.

    -- -- In the class TypesOfVar we associated to the variables bounded
    -- -- in Lam terms the type DontCare.
    -- El (Type (Max [])) DontCare → return ty

    -- Because the variable is not a proof term we don't do anything.
    El (Type (Max []))
       (Pi (Dom _ _ (El (Type (Max [])) (Def _ [])))
           (NoAbs _ (El (Type (Max [])) (Def _ [])))
       ) → return ty

    -- The next case is just a generalization to various arguments of
    -- the previous case.

    -- The variable's type is a function type,
    --
    -- e.g. the variable is f : D → D → D, where D : Set.

    -- Because the variable is not a proof term we don't do anything.
    El (Type (Max []))
       (Pi (Dom _ _ (El (Type (Max [])) (Def _ [])))
           (NoAbs _ (El (Type (Max [])) (Pi _ (NoAbs _ _))))
       ) → return ty

    -- We don't erase these proofs terms.
    El (Type (Max [])) someTerm → do
      reportSLn "dropPT" 20 $
                "The term someTerm is: " ++ show someTerm
      throwError $ "It is necessary to erase the proof term\n"
                   ++ showLn someTerm
                   ++ "but we do not know how to do it"

    -- The variable's type is Set₁,
    --
    -- e.g. the variable is P : Set.
    --
    -- Because the variable is not a proof term we don't do anything.
    El (Type (Max [ClosedLevel 1])) (Sort _) → return ty

    -- N.B. The next case is just a generalization to various
    -- arguments of the previous case.

    -- The variable's type is Set₁,
    --
    -- e.g. the variable is P : D → Set.
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
      reportSLn "dropPT" 20 $
                "The type varType is: " ++ show someType
      __IMPOSSIBLE__
