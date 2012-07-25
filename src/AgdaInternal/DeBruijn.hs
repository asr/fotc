------------------------------------------------------------------------------
-- |
-- Module      : AgdaInternal.DeBruijn
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
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

-- There are various cases (e.g. eta-expansion, translation of
-- symbols' definitions, elimination of quantification on variables
-- which are proof terms) where it is necessary modify the variables
-- in the Agda internal terms, i.e. it is necessary to modify the
-- Bruijn index in the variable.

module AgdaInternal.DeBruijn
  ( ChangeIndex(changeIndex)
  , DecIndex(decIndex)
  , IncIndex(incIndex)
  , varToIndex
  )
  where

------------------------------------------------------------------------------
-- Haskell imports

import Data.List ( elemIndex )

------------------------------------------------------------------------------
-- Agda libray imports

import Agda.Syntax.Common ( Arg(Arg), Dom(Dom), Nat )

import Agda.Syntax.Internal
  ( Abs(Abs, NoAbs)
  , Args
  , ClauseBody(Bind,Body)
  , Level(Max)
  , Tele(EmptyTel, ExtendTel)
  , Term(Def, Lam, Var)
  , Sort(Type)
  , Type(El)
  , var
  )

import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )

------------------------------------------------------------------------------
-- Local imports

#include "../undefined.h"

------------------------------------------------------------------------------
-- | To increase by one the de Bruijn index of the variable in an Agda
-- entity.
class IncIndex a where
  incIndex ∷ a → a

instance IncIndex Term where
  incIndex (Var n [])  = var (n + 1)
  incIndex (Var _ _)   = __IMPOSSIBLE__
  incIndex _           = __IMPOSSIBLE__

instance IncIndex a ⇒ IncIndex (Arg a) where
  incIndex (Arg h r e) = Arg h r $ incIndex e

------------------------------------------------------------------------------
-- | To decrease by one the de Bruijn index of the variable in an Agda
-- entity.
class DecIndex a where
  decIndex ∷ a → a

instance DecIndex Term where
  decIndex (Def qname args) = Def qname $ decIndex args
  decIndex (Var 0 [])       = __IMPOSSIBLE__
  decIndex (Var n [])       = var (n - 1)
  decIndex (Var _ _)        = __IMPOSSIBLE__
  decIndex _                = __IMPOSSIBLE__

instance DecIndex a ⇒ DecIndex [a] where
  decIndex = map decIndex

instance DecIndex Type where
  decIndex (El (Type (Max [])) term) = El (Type (Max [])) (decIndex term)
  decIndex _                         = __IMPOSSIBLE__

instance DecIndex a ⇒ DecIndex (Arg a) where
  decIndex (Arg h r e) = Arg h r $ decIndex e

instance DecIndex a ⇒ DecIndex (Dom a) where
  decIndex (Dom h r e) = Dom h r $ decIndex e

instance DecIndex a ⇒ DecIndex (Abs a) where
  decIndex (Abs name body) = Abs name $ decIndex body
  decIndex (NoAbs _ _)     = __IMPOSSIBLE__

instance DecIndex a ⇒ DecIndex (Tele a) where
  -- 31 May 2012. We don't have an example of this case.
  --
  -- decIndex EmptyTel          = EmptyTel
  decIndex EmptyTel          = __IMPOSSIBLE__
  decIndex (ExtendTel a tel) = ExtendTel (decIndex a) (decIndex tel)

------------------------------------------------------------------------------
-- We collect the variables' names using the type class VarNames. The
-- de Bruijn indexes are assigned from right to left,
--
-- e.g.  in @(A B C : Set) → ...@, @A@ is 2, @B@ is 1, and @C@ is 0,
--
-- so we need create the list in the same order.

class VarNames a where
  varNames ∷ a → [String]

instance VarNames Term where
  varNames (Def _ args) = varNames args

  varNames (Lam _ (Abs x term)) = varNames term ++ [x]

  varNames (Var _ []) = []
  -- 31 May 2012. We don't have an example of this case.
  --
  -- varNames (Var _ args) = varNames args
  varNames (Var _ _) = __IMPOSSIBLE__
  varNames _         = __IMPOSSIBLE__

instance VarNames a ⇒ VarNames (Arg a) where
  varNames (Arg _ _ e) = varNames e

instance VarNames a ⇒ VarNames [a] where
  varNames = concatMap varNames

instance VarNames ClauseBody where
  varNames (Bind (Abs x cBody)) = varNames cBody ++ [x]
  varNames (Body term)          = varNames term
  varNames _                    = __IMPOSSIBLE__

-- | Return the de Bruijn index of a variable in a 'ClauseBody'.
varToIndex ∷ ClauseBody → String → Nat
varToIndex cBody x =
  case elemIndex x (varNames cBody) of
    Just n  → fromIntegral n
    Nothing → __IMPOSSIBLE__

------------------------------------------------------------------------------
-- | To change a de Bruijn index with respect to other index in an
-- Agda entity.

-- Let's suppose we have something like

-- @λ m : D → (λ n : D → (λ Nn : N n → (λ h : D → ... Var 2 ...)))@

-- where @Var 2@ is the de Bruijn index of the variable @n@. If we
-- drop the quantification on the proof term @Nn@

-- @λ m : D → (λ n : D → (λ h : D → ...))@

-- we need change @Var 2@ by @Var 1@.

class ChangeIndex a where
  changeIndex ∷ a → Nat → a

instance ChangeIndex Term where
  changeIndex term@(Def _ []) _ = term

  changeIndex (Def qName args) index = Def qName $ changeIndex args index

  changeIndex (Lam h (Abs x term)) index = Lam h (Abs x (changeIndex term index))

  -- When the variable is part of an argument, it was processed in the
  -- Args instance.
  changeIndex (Var n []) index
    -- The variable was after than the quantified variable, we need
    -- "unbound" the quantified variable.
    | n > index = var (n - 1)

    -- In the case @n < index@ the variable was before than the
    -- quantified variable, therefore we shouldn't do nothing, i.e. we
    -- should return the term.
    | otherwise = __IMPOSSIBLE__

  changeIndex _ _ = __IMPOSSIBLE__

-- In the Agda source code (Agda.Syntax.Internal) we have
--
-- type Args = [Arg Term]
--
-- however, we cannot create the instance of Args based on a simple
-- map, because in some cases we need to erase the term.

-- Requires @TypeSynonymInstances@ and @FlexibleInstances@.
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
