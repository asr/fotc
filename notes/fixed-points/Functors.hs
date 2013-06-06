{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module Functor where

-- Based on (Vene, 2000).

-- References:
--
-- • Varmo Vene. Categorical programming with inductive and
-- coinductive types. PhD thesis, University of Taru, Estonia, 2000.

import Prelude hiding ( pred )

------------------------------------------------------------------------------
-- The least fixed-point of the (unary) type constructor f.
data Mu f = Functor f ⇒ In (f (Mu f))

unIn ∷ Functor f ⇒ Mu f → f (Mu f)
unIn (In x) = x

-- The greatest fixed-point of the (unary) type constructor f.
data Nu f = Functor f ⇒ Wrap (f (Nu f))

out ∷ Functor f ⇒ Nu f → f (Nu f)
out (Wrap x) = x

------------------------------------------------------------------------------
-- Functors

--  The identity functor (the functor for the empty and unit types).
newtype IdF x = MkIdF x

instance Functor IdF where
  fmap f (MkIdF x) = MkIdF (f x)

-- The (co)natural numbers functor.
data NatF x = Z | S x

instance Functor NatF where
  fmap _ Z     = Z
  fmap f (S x) = S (f x)

-- The (co)list functor.
data ListF a x = Nil | Cons a x

instance Functor (ListF a) where
  fmap _ Nil         = Nil
  fmap f (Cons x xs) = Cons x (f xs)

-- The stream functor.
data FS a x = St a x

instance Functor (FS a) where
  fmap f (St a x) = St a (f x)

------------------------------------------------------------------------------
-- Types as least fixed-points

-- The empty type is a least fixed-point.
type Empty = Mu IdF

-- NB. It seems we can create an term of type Empty using
-- non-structural recursion.
empty ∷ Empty
empty = In (MkIdF empty)

-- The natural numbers type is a least fixed-point.
type Nat = Mu NatF

-- The data constructors for the natural numbers.
zero ∷ Nat
zero = In Z

succ ∷ Nat → Nat
succ n = In (S n)

-- The list type is a least fixed-point.
type List a = Mu (ListF a)

-- The data constructors for List.
nil ∷ List a
nil = In Nil

cons ∷ a → List a → List a
cons x xs = In (Cons x xs)

------------------------------------------------------------------------------
-- Types as greatest fixed-points

-- The unit type is a greatest fixed-point.
type Unit = Nu IdF

unit ∷ Unit
unit = Wrap (MkIdF unit)  -- Non-structural recursion.

-- The unit type destructor.
idUnit ∷ Unit → Unit
idUnit u = u

-- The conaturals type is a greatest fixed-point.
type Conat = Nu NatF

instance Eq Conat where
  Wrap Z     == Wrap Z     = True
  Wrap Z     == _          = False
  Wrap (S m) == Wrap (S n) = m == n
  Wrap (S _) == _          = False

instance Show Conat where
  show (Wrap Z)     = "zero"
  show (Wrap (S m)) = "s(" ++ show m ++ ")"

zeroC ∷ Conat
zeroC = Wrap Z

succC ∷ Conat → Conat
succC n = Wrap (S n)

inftyC ∷ Conat
inftyC = succC inftyC

data ConatPlusOne = One | MkConat Conat
                    deriving Show

-- TODO: The conat destructor.
pred ∷ Conat → ConatPlusOne
pred cn
  | cn == inftyC = MkConat inftyC
  | otherwise    = case out cn of
                     Z   → One
                     S x → MkConat x

-- The colist type is a greatest fixed-point.
type Colist a = Nu (ListF a)

-- The colist data constructors.
nilCL ∷ Colist a
nilCL = Wrap Nil

consCL ∷ a → Colist a → Colist a
consCL x xs = Wrap (Cons x xs)

-- The colist destructors.
nullCL ∷ Colist a → Bool
nullCL xs = case out xs of
              Nil      → True
              Cons _ _ → False

headCL ∷ Colist a → a
headCL xs = case out xs of
              Nil     → error "Impossible"
              Cons x _ → x

tailCL ∷ Colist a → Colist a
tailCL xs = case out xs of
              Nil       → error "Impossible"
              Cons _ xs' → xs'

-- The stream type is a greatest fixed-point.
type Stream a = Nu (FS a)

-- The stream data constructor.
consS ∷ a → Stream a → Stream a
consS x xs = Wrap (St x xs)

-- The stream destructors.
headS ∷ Stream a → a
headS xs = case out xs of
             St x _ → x

tailS ∷ Stream a → Stream a
tailS xs = case out xs of
             St _ xs' → xs'
