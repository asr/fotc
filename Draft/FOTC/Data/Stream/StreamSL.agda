------------------------------------------------------------------------------
-- Definition of FOTC streams using the Agda coinductive combinators
------------------------------------------------------------------------------

-- Tested with the development version Agda and the standard library
-- on 26 September 2011.

module StreamSL where

open import Data.Product renaming ( _×_ to _∧_ )
open import Coinduction
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

data D : Set where
  _∷_ : D → D → D

data Stream : D → Set where
  consS : ∀ x {xs} → ∞ (Stream xs) → Stream (x ∷ xs)

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
