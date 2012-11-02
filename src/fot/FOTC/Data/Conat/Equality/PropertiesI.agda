------------------------------------------------------------------------------
-- Properties for the equality on Conat
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • Herbert P. Sander. A logic of functional programs with an
--   application to concurrency. PhD thesis, Chalmers University of
--   Technology and University of Gothenburg, Department of Computer
--   Sciences, 1992.

module FOTC.Data.Conat.Equality.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Data.List
open import FOTC.Data.Stream

------------------------------------------------------------------------------

≈N-refl : ∀ {n} → Conat n → n ≈N n
≈N-refl {n} Cn = ≈N-coind R h₁ h₂
  where
  R : D → D → Set
  R a b = Conat a ∧ Conat b ∧ a ≡ b

  h₁ : ∀ {a b} → R a b →
       a ≡ zero ∧ b ≡ zero
       ∨ (∃ (λ a' → ∃ (λ b' → R a' b' ∧ a ≡ succ₁ a' ∧ b ≡ succ₁ b')))
  h₁ (Ca , Cb , refl) with Conat-unf Ca
  ... | inj₁ prf              = inj₁ (prf , prf)
  ... | inj₂ (a' , Ca' , prf) = inj₂ (a' , a' , (Ca' , Ca' , refl) , (prf , prf))

  h₂ : Conat n ∧ Conat n ∧ n ≡ n
  h₂ = Cn , Cn , refl

≡→≈N : ∀ {m n} → Conat m → Conat n → m ≡ n → m ≈N n
≡→≈N h _ refl = ≈N-refl h

-- Adapted from (Sander 1992, p. 58).
stream-length : ∀ {xs} → Stream xs → length xs ≈N ∞
stream-length {xs} Sxs = ≈N-coind R h₁ h₂
  where
  R : D → D → Set
  R m n = m ≡ zero ∧ n ≡ zero ∨ (∃[ ys ] Stream ys ∧ m ≡ length ys ∧ n ≡ ∞)

  h₁ : ∀ {m n} → R m n →
       m ≡ zero ∧ n ≡ zero
       ∨ (∃[ m' ] ∃[ n' ] R m' n' ∧ m ≡ succ₁ m' ∧ n ≡ succ₁ n')
  h₁ (inj₁ prf) = inj₁ prf
  h₁ {m} {n} (inj₂ (ys , Sys , h₁ , h₂)) with Stream-unf Sys
  ... | y' , ys' , Sys' , ys≡y'∷ys' =
    inj₂ ((length ys') , (n , ((inj₂ (ys' , Sys' , refl , h₂)) , (prf₁ , prf₂))))
    where
    prf₁ : m ≡ succ₁ (length ys')
    prf₁ = trans₂ h₁ (cong length ys≡y'∷ys') (length-∷ y' ys')

    prf₂ : n ≡ succ₁ n
    prf₂ = trans₂ h₂ ∞-eq (succCong (sym h₂))

  h₂ : R (length xs) ∞
  h₂ = inj₂ (xs , Sxs , refl , refl)
