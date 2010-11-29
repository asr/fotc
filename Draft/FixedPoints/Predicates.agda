module Draft.FixedPoints.Predicates where

open import LTC.Base

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

-- The (least fixed-point) LTC natural numbers.
module LeastFixedPoint where

  postulate
    -- Least fixed-points correspond to inductively defined predicates.
    -- N.B. We cannot write LFP in first order logic.
    LFP : ((D → Set) → D → Set) → D → Set

    -- In the first-order version of LTC we cannot use the equality on
    -- predicates
    --
    -- (i.e. _≣_ : (D → Set) → (D → Set) → Set),
    --
    -- therefore we postulate both directions of the conversion rule
    -- LFP f = f (LFP f).
    LFP₁ : (f : (D → Set) → D → Set) → (d : D) → LFP f d → f (LFP f) d
    LFP₂ : (f : (D → Set) → D → Set) → (d : D) → f (LFP f) d → LFP f d

  -- Because N is an inductive predicate, we can defined it as the least
  -- fixed-point of an appropriate functor.

  -- The LTC natural numbers functor FN

  -- From Peter: FN if D was an inductive type
  -- FN : (D → Set) → D → Set
  -- FN X zero     = ⊤
  -- FN X (succ n) = X n

  -- From Peter: FN in pure predicate logic
  FN : (D → Set) → D → Set
  FN X n = n ≡ zero ∨ ∃D λ m → n ≡ succ m ∧ X m

  -- The LTC natural numbers using LFP.
  N : D → Set
  N = LFP FN

  -- The data constructors of the inductive version via the
  -- least fixed-point version.
  zN : N zero
  zN = LFP₂ FN zero (inj₁ refl)

  sN : {n : D} → N n → N (succ n)
  sN {n} Nn = LFP₂ FN (succ n) (inj₂ (n , (refl , Nn)))
