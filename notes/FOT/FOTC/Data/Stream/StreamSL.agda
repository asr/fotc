------------------------------------------------------------------------------
-- Definition of FOTC streams using the Agda coinductive combinators
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of the standard library on
-- 11 June 2012.

module StreamSL where

open import Data.Product renaming ( _×_ to _∧_ )
open import Coinduction
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

data D : Set where
  _∷_ : D → D → D

data Stream : D → Set where
  consS : ∀ x {xs} → ∞ (Stream xs) → Stream (x ∷ xs)

Stream-gfp₁ : ∀ {xs} → Stream xs →
              ∃ λ x' → ∃ λ xs' → Stream xs' ∧ xs ≡ x' ∷ xs'
Stream-gfp₁ (consS x' {xs'} Sxs') = x' , xs' , ♭ Sxs' , refl

Stream-gfp₂ : (P : D → Set) →
              -- P is post-fixed point of StreamF.
              (∀ {xs} → P xs → ∃ λ x' → ∃ λ xs' → P xs' ∧ xs ≡ x' ∷ xs') →
              -- Stream is greater than P.
              ∀ {xs} → P xs → Stream xs
Stream-gfp₂ P h {xs} Pxs = subst Stream (sym xs≡x'∷xs') prf
  where
    x' : D
    x' = proj₁ (h Pxs)

    xs' : D
    xs' = proj₁ (proj₂ (h Pxs))

    Pxs' : P xs'
    Pxs' = proj₁ (proj₂ (proj₂ (h Pxs)))

    xs≡x'∷xs' : xs ≡ x' ∷ xs'
    xs≡x'∷xs' = proj₂ (proj₂ (proj₂ (h Pxs)))

    prf : Stream (x' ∷ xs')
    prf = consS x' (♯ (Stream-gfp₂ P h Pxs'))
