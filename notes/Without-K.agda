------------------------------------------------------------------------------
-- Testing the --without-K flag
------------------------------------------------------------------------------

-- Tested with Agda 2.3.1 on 15 December 2011.

-- {-# OPTIONS --without-K #-}

module Without-K where

-- The following code fails with the --without-K flag.

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ x → x ≡ x

K : {A : Set} (P : {x : A} → x ≡ x → Set) →
    (∀ x → P (refl x)) →
    ∀ {x} (x≡x : x ≡ x) → P x≡x
K P p (refl x) = p x
