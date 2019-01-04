------------------------------------------------------------------------------
-- Definition of FOTC streams using the Agda co-inductive combinators
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Data.Stream.TypeSL where

open import Codata.Musical.Notation
open import Data.Product renaming ( _×_ to _∧_ )
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Data/List.agda).
infixr 8 _∷_

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
