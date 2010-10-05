module Others.FixedPoints where

open import LTC.Minimal

------------------------------------------------------------------------------

-- The pure (i.e. non-inductive) LTC natural numbers.
module Pure where
  postulate
    N  : D → Set
    zN : N zero
    sN : {n : D} → N n → N (succ n)

-- The (inductive) LTC natural numbers.
module Inductive where

  data N : D → Set where
    zN : N zero
    sN : {n : D} → N n → N (succ n)

-- The (fixed-point) LTC natural numbers.
module FixedPoint where

  -- Because N is an inductive data type, we can defined it as the least
  -- fixed-point (Fix) of an appropriate functional.
  postulate
    Fix : ((D → Set) → D → Set) → D → Set
    -- In the first-order version of LTC we cannot use the equality on
    -- predicates
    --
    -- (i.e. _≣_ : (D → Set) → (D → Set) → Set),
    --
    -- therefore we postulate both directions of the conversion rule
    -- Fix f = f (Fix f).
    cFix₁ : (f : (D → Set) → D → Set) → (d : D) → Fix f d → f (Fix f) d
    cFix₂ : (f : (D → Set) → D → Set) → (d : D) → f (Fix f) d → Fix f d

  -- From Peter: FN if D was an inductive type
  -- FN : (D → Set) → D → Set
  -- FN X zero     = ⊤
  -- FN X (succ n) = X n

  -- From Peter: FN in pure predicate logic
  FN : (D → Set) → D → Set
  FN X n = n ≡ zero ∨ (∃D (λ m → n ≡ succ m ∧ X m))

  -- The LTC natural numbers using Fix.
  N : D → Set
  N = Fix FN

  -- The data constructors of the inductive version via the
  -- fixed-point version.
  zN : N zero
  zN = cFix₂ FN zero (inj₁ refl)

  sN : {n : D} → N n → N (succ n)
  sN {n} Nn = cFix₂ FN (succ n) (inj₂ (n , (refl , Nn)))
