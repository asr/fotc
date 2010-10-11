-- Tested with GHC 6.12.3.

{-# LANGUAGE ExistentialQuantification #-}
-- {-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UnicodeSyntax #-}

-- Based on [1].

-- [1] Varmo Vene. Categorical programming with inductive and
-- coinductive types. PhD thesis, University of Taru, Estonia, 2000.

------------------------------------------------------------------------------
-- The least fixed-point of the (unary) type constructor f.
data Mu f = Functor f ⇒ In (f (Mu f))

unIn :: Functor f ⇒ Mu f → f (Mu f)
unIn (In x) = x

-- The greatest fixed-point of the (unary) type constructor f.
data Nu f = Functor f ⇒ Wrap (f (Nu f))

out :: Functor f ⇒ Nu f → (f (Nu f))
out (Wrap x) = x

------------------------------------------------------------------------------
-- Functors

--  The identity functor (the functor for the empty and unit types).
newtype FId x = MkFId x

instance Functor FId where
    fmap f (MkFId x) = MkFId (f x)

-- The (co)natural numbers functor.
data FN x = Z | S x

instance Functor FN where
    fmap _ Z     = Z
    fmap f (S x) = S (f x)

-- The (co)list functor.
data FL a x = N | C a x

instance Functor (FL a) where
    fmap _ N        = N
    fmap f (C x xs) = C x (f xs)

-- The stream functor.
data FS a x = St a x

instance Functor (FS a) where
    fmap f (St a x) = St a (f x)

------------------------------------------------------------------------------
-- Types as least fixed-points

-- The empty type is a least fixed-point.
type Empty = Mu FId

-- NB. It seems we can create an term of type Empty using
-- non-structural recursion.
empty :: Empty
empty = In (MkFId empty)


-- The natural numbers type is a least fixed-point.
type N = Mu FN

-- The data constructors for the natural numbers.
zero :: N
zero = In Z

succ :: N → N
succ n = In (S n)

-- The list type is a least fixed-point.
type List a = Mu (FL a)

-- The data constructors for List.
nil :: List a
nil = In N

cons :: a → List a → List a
cons x xs = In (C x xs)

------------------------------------------------------------------------------
-- Types as greatest fixed-points

-- The unit type is a greatest fixed-point.
type Unit = Nu FId

unit :: Unit
unit = Wrap (MkFId unit)  -- Non-structural recursion.

-- The unit type destructor.
idUnit :: Unit → Unit
idUnit u = u

-- The conaturals type is a greatest fixed-point.
type Conat = Nu FN

data ConatPlusOne = One | MkConat Conat

-- TODO: The conat destructor.
pred :: Conat → ConatPlusOne
pred cn = case out cn of
            Z   → One
            S x → MkConat x

-- The colist type is a greatest fixed-point.
type Colist a = Nu (FL a)

-- The colist destructors.
nullCL :: Colist a → Bool
nullCL xs = case out xs of
              N     → True
              C _ _ → False

headCL :: Colist a → a
headCL xs = case out xs of
              C x _ → x

tailCL :: Colist a → Colist a
tailCL xs = case out xs of
             C _ xs' → xs'

-- The stream type is a greatest fixed-point.
type Stream a = Nu (FS a)

-- The stream destructors.
headS :: Stream a → a
headS xs = case out xs of
             St x _ → x

tailS :: Stream a → Stream a
tailS xs = case out xs of
             St _ xs' → xs'
