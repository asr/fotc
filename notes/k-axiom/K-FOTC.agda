{-# OPTIONS --no-universe-polymorphism #-}
-- {-# OPTIONS --without-K                #-}  -- No accepted!

module K-FOTC where

postulate D : Set

data _≡_ (x : D) : D → Set where
  refl : x ≡ x

K : (x : D)(P : x ≡ x → Set) → P refl → (p : x ≡ x) → P p
K x P pr refl = pr
