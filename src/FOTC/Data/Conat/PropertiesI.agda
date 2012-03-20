------------------------------------------------------------------------------
-- Conat properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • Herbert P. Sander. A logic of functional programs with an
--   application to concurrency. PhD thesis, Chalmers University of
--   Technology and University of Gothenburg, Department of Computer
--   Sciences, 1992.

module FOTC.Data.Conat.PropertiesI where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.Stream

------------------------------------------------------------------------------

0-Conat : Conat zero
0-Conat = Conat-gfp₂ P helper refl
  where
  P : D → Set
  P n = n ≡ zero

  helper : ∀ {n} → P n → n ≡ zero ∨ (∃[ n' ] P n' ∧ n ≡ succ₁ n')
  helper Pn = inj₁ Pn

-- Adapted from (Sander 1992, p. 57).
ω-Conat : Conat ω
ω-Conat = Conat-gfp₂ P helper refl
  where
  P : D → Set
  P n = n ≡ ω

  helper : ∀ {n} → P n → n ≡ zero ∨ (∃[ n' ] P n' ∧ n ≡ succ₁ n')
  helper Pn = inj₂ (ω , refl , trans Pn ω-eq)

-- Adapted from (Sander 1992, p. 58).
stream-length : ∀ {xs} → Stream xs → length xs ≈N ω
stream-length {xs} Sxs = ≈N-gfp₂ _R_ helper₁ helper₂
  where
  _R_ : D → D → Set
  m R n = m ≡ zero ∧ n ≡ zero ∨ (∃[ ys ] Stream ys ∧ m ≡ length ys ∧ n ≡ ω)

  helper₁ : ∀ {m n} → m R n →
            m ≡ zero ∧ n ≡ zero
            ∨ (∃[ m' ] ∃[ n' ] m' R n' ∧ m ≡ succ₁ m' ∧ n ≡ succ₁ n')
  helper₁ (inj₁ prf) = inj₁ prf
  helper₁ {m} {n} (inj₂ (ys , Sys , h₁ , h₂)) with Stream-gfp₁ Sys
  ... | y' , ys' , Sys' , ys≡y'∷ys' =
    inj₂ ((length ys') , (n , ((inj₂ (ys' , Sys' , refl , h₂)) , (prf₁ , prf₂))))
    where
    prf₁ : m ≡ succ₁ (length ys')
    prf₁ = trans₂ h₁ (cong length ys≡y'∷ys') (length-∷ y' ys')

    prf₂ : n ≡ succ₁ n
    prf₂ = trans₂ h₂ ω-eq (cong succ₁ (sym h₂))

  helper₂ : length xs R ω
  helper₂ = inj₂ (xs , Sxs , refl , refl)
