{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module StrictlyPositive where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

------------------------------------------------------------------------------
-- Parametric stability constraint (Coq Art, p. 378).

-- Error: B != A of type Set when checking the constructor c in the
-- declaration of T

-- data T (A : Set) : Set where
--   c : (B : Set) → T B

------------------------------------------------------------------------------
-- Head type constraint (Coq Art, section 14.1.2.1).

-- Error: T is not strictly positive, because it occurs in an index of
-- the target type of the constructor c in the definition of T.
-- data T : Set → Set where
--   c : T (T ℕ)

------------------------------------------------------------------------------
-- Strictly positive constraints (Coq Art, section 14.1.2.2).

-- Error: A is not strictly positive, because it occurs to the left of
-- an arrow in the type of the constructor c in the definition of A.
--
-- data A : Set where
--   c : (A → A) → A

------------------------------------------------------------------------------
-- Universe constraints (Coq Art, section 14.1.2.3).

record R : Set₁ where
  field
    A  : Set
    op : A → A → A
    e  : A

-- Nils (Agda mailing list): According to Voevodsky this type is
-- incompatible with his univalent model.
data _≡_ (A : Set) : Set → Set where
  refl : A ≡ A

data A : Set → Set where
  c : A ℕ
