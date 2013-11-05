------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • Sander, Herbert P. (1992). A Logic of Functional Programs with an
--   Application to Concurrency. PhD thesis. Department of Computer
--   Sciences: Chalmers University of Technology and University of
--   Gothenburg.

module FOTC.Data.Stream.PropertiesI where

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.Stream

-----------------------------------------------------------------------------

tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
tailS h with Stream-unf h
... | x' , xs' , h₁ , Sxs' = subst Stream (sym (∧-proj₂ (∷-injective h₁))) Sxs'

-- Adapted from (Sander 1992, p. 58).
streamLength : ∀ {xs} → Stream xs → length xs ≈N ∞
streamLength {xs} Sxs = ≈N-coind R h₁ h₂
  where
  R : D → D → Set
  R m n = m ≡ zero ∧ n ≡ zero ∨ (∃[ xs' ] m ≡ length xs' ∧ n ≡ ∞ ∧ Stream xs')

  h₁ : ∀ {m n} → R m n →
       m ≡ zero ∧ n ≡ zero
         ∨ (∃[ m' ] ∃[ n' ] m ≡ succ₁ m' ∧ n ≡ succ₁ n' ∧ R m' n')
  h₁ (inj₁ prf) = inj₁ prf
  h₁ {m} {n} (inj₂ (xs' , prf₁ , prf₂ , Sxs')) with Stream-unf Sxs'
  ... | x'' , xs'' , xs'≡x''∷xs'' , Sxs'' =
    inj₂ (length xs'' , n , helper₁ , helper₂ , inj₂ (xs'' , refl , prf₂ , Sxs''))

    where
    helper₁ : m ≡ succ₁ (length xs'')
    helper₁ = trans₂ prf₁ (lengthCong xs'≡x''∷xs'') (length-∷ x'' xs'')

    helper₂ : n ≡ succ₁ n
    helper₂ = trans₂ prf₂ ∞-eq (succCong (sym prf₂))

  h₂ : R (length xs) ∞
  h₂ = inj₂ (xs , refl , refl , Sxs)
