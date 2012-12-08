------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • Herbert P. Sander. A logic of functional programs with an
--   application to concurrency. PhD thesis, Chalmers University of
--   Technology and University of Gothenburg, Department of Computer
--   Sciences, 1992.

module FOTC.Data.Stream.PropertiesI where

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.List
open import FOTC.Data.Stream

-----------------------------------------------------------------------------

tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
tailS h with (Stream-unf h)
... | x' , xs' , Sxs' , h₁ = subst Stream (sym (∧-proj₂ (∷-injective h₁))) Sxs'

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
