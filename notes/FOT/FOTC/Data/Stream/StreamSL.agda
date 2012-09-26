------------------------------------------------------------------------------
-- Definition of FOTC streams using the Agda co-inductive combinators
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Stream.StreamSL where

open import Data.Product renaming ( _×_ to _∧_ )
open import Coinduction
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

data D : Set where
  _∷_ : D → D → D

data Stream : D → Set where
  consS : ∀ x {xs} → ∞ (Stream xs) → Stream (x ∷ xs)

Stream-unf : ∀ {xs} → Stream xs →
             ∃ λ x' → ∃ λ xs' → Stream xs' ∧ xs ≡ x' ∷ xs'
Stream-unf (consS x' {xs'} Sxs') = x' , xs' , ♭ Sxs' , refl

{-# NO_TERMINATION_CHECK #-}
Stream-coind : (A : D → Set) →
             -- A is post-fixed point of StreamF.
             (∀ {xs} → A xs → ∃ λ x' → ∃ λ xs' → A xs' ∧ xs ≡ x' ∷ xs') →
             -- Stream is greater than A.
             ∀ {xs} → A xs → Stream xs
Stream-coind A h {xs} Axs = subst Stream (sym xs≡x'∷xs') prf
  where
    x' : D
    x' = proj₁ (h Axs)

    xs' : D
    xs' = proj₁ (proj₂ (h Axs))

    Axs' : A xs'
    Axs' = proj₁ (proj₂ (proj₂ (h Axs)))

    xs≡x'∷xs' : xs ≡ x' ∷ xs'
    xs≡x'∷xs' = proj₂ (proj₂ (proj₂ (h Axs)))

    prf : Stream (x' ∷ xs')
    prf = consS x' (♯ (Stream-coind A h Axs'))
