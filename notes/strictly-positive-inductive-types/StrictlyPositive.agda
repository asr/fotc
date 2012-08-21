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
-- Strictly positive constraints (Coq Art, section 14.1.2).

-- NB. This type is not accepted by Coq.
data T : Set → Set where
  c : T (T ℕ)

-- Error: A is not strictly positive, because it occurs to the left of
-- an arrow in the type of the constructor c in the definition of A.
--
-- data A : Set where
--   c : (A → A) → A
