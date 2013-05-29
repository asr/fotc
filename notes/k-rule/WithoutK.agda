------------------------------------------------------------------------------
-- Testing the --without-K flag
------------------------------------------------------------------------------

-- {-# OPTIONS --without-K #-}

module WithoutK where

-- The following code fails with the --without-K flag.

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ x → x ≡ x

K : {A : Set} (P : {x : A} → x ≡ x → Set) →
    (∀ x → P (refl x)) →
    ∀ {x} (x≡x : x ≡ x) → P x≡x
K P p (refl x) = p x
