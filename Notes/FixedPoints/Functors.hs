-- Tested with GHC 6.12.3.

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UnicodeSyntax #-}

-- Based on [1].

-- [1] Varmo Vene. Categorical programming with inductive and
-- coinductive types. PhD thesis, University of Taru, Estonia, 2000.

------------------------------------------------------------------------------

-- The least fixed-point of the type constructor f.
data Mu f = Functor f ⇒ In (f (Mu f))

unIn :: Functor f ⇒ Mu f → f (Mu f)
unIn (In x) = x

-- The greatest fixed-point of the type constructor f.
data Nu f = Functor f ⇒ Wrap (f (Nu f))

out :: Functor f ⇒ Nu f → (f (Nu f))
out (Wrap x) = x

------------------------------------------------------------------------------

-- The empty functor.
newtype FE x = MkFe x

instance Functor FE where
    fmap f (MkFe x) = MkFe (f x)

-- The empty type is a least fixed-point.
type Empty = Mu FE

------------------------------------------------------------------------------

-- The natural numbers functor.
data FN x = Z | S x

instance Functor FN where
    fmap _ Z     = Z
    fmap f (S x) = S (f x)

-- The natural numbers type is a least fixed-point.
type N = Mu FN

-- The data constructors for the natural numbers.
zero :: N
zero = In Z

succ :: N → N
succ n = In (S n)

------------------------------------------------------------------------------

-- The list functor.
data FL a x = N | C a x

instance Functor (FL a) where
    fmap _ N        = N
    fmap f (C x xs) = C x (f xs)

-- The list type is a least fixed-point.
type List a = Mu (FL a)

-- The data constructors for List.
nil :: List a
nil = In N

cons :: a → List a → List a
cons x xs = In (C x xs)

------------------------------------------------------------------------------

-- The conaturals type is a greatest fixed-point.
type Conat = Nu FN

data ConatPlusOne = One | MkConat Conat

-- TODO: The conat destructor.
pred :: Conat → ConatPlusOne
pred cn = case out cn of
            Z   → One
            S x → MkConat x

------------------------------------------------------------------------------

-- The stream functor.
data FS a x = St a x

instance Functor (FS a) where
    fmap f (St a x) = St a (f x)

-- The stream type is a greatest fixed-point.
type Stream a = Nu (FS a)

-- The stream destructors.
head :: Stream a → a
head xs = case out xs of
            St x _ → x

tail :: Stream a → Stream a
tail xs = case out xs of
            St _ xs' → xs'
