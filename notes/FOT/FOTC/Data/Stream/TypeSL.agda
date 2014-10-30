------------------------------------------------------------------------------
-- Definition of FOTC streams using the Agda co-inductive combinators
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Data.Stream.TypeSL where

open import Data.Product renaming ( _×_ to _∧_ )
open import Coinduction
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

data D : Set where
  _∷_ : D → D → D

data Stream : D → Set where
  consS : ∀ x {xs} → ∞ (Stream xs) → Stream (x ∷ xs)

Stream-out : ∀ {xs} → Stream xs →
             ∃ λ x' → ∃ λ xs' → Stream xs' ∧ xs ≡ x' ∷ xs'
Stream-out (consS x' {xs'} Sxs') = x' , xs' , ♭ Sxs' , refl

{-# NON_TERMINATING #-}
Stream-coind :
  (A : D → Set) →
  (∀ {xs} → A xs → ∃ λ x' → ∃ λ xs' → xs ≡ x' ∷ xs' ∧ A xs') →
  ∀ {xs} → A xs → Stream xs
Stream-coind A h Axs with h Axs
... | x' , xs' , prf₁ , Axs' = subst Stream (sym prf₁) prf₂
  where
  prf₂ : Stream (x' ∷ xs')
  prf₂ = consS x' (♯ Stream-coind A h Axs')
