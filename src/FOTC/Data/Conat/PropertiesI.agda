------------------------------------------------------------------------------
-- Conat properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Conat.PropertiesI where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.Stream

------------------------------------------------------------------------------

-- Adapted from Herbert's thesis, p. 57.
ω-Conat : Conat ω
ω-Conat = Conat-gfp₂ P helper refl
  where
  P : D → Set
  P n = n ≡ ω

  helper : ∀ {n} → P n → ∃[ n' ] P n' ∧ n ≡ succ₁ n'
  helper Pn = ∃-intro (refl , trans Pn ω-eq)

-- Adapted from Herbert's thesis, p. 58.
stream-length : ∀ {xs} → Stream xs → length xs ≈N ω
stream-length {xs} Sxs = ≈N-gfp₂ _R_ helper₁ helper₂
  where
  _R_ : D → D → Set
  m R n = ∃[ ys ] Stream ys ∧ m ≡ length ys ∧ n ≡ ω

  -- 2012-02-29. The existential witnesses could be avoid not using
  -- the auxiliary proofs inside the where clause.
  helper₁ : ∀ {m n} → m R n →
            ∃[ m' ] ∃[ n' ] m' R n' ∧ m ≡ succ₁ m' ∧ n ≡ succ₁ n'
  helper₁ {m} {n} (∃-intro (Sys , h₁ , h₂)) with Stream-gfp₁ Sys
  ... | ∃-intro {y'} (∃-intro {ys'} (Sys' , ys≡y'∷ys')) =
    ∃-intro (∃-intro ((∃-intro (Sys' , refl , h₂)) , (prf₁ , prf₂)))
    where
    prf₁ : m ≡ succ₁ (length ys')
    prf₁ = trans₂ h₁ (cong length ys≡y'∷ys') (length-∷ y' ys')

    prf₂ : n ≡ succ₁ n
    prf₂ = trans₂ h₂ ω-eq (cong succ₁ (sym h₂))

  helper₂ : length xs R ω
  helper₂ = ∃-intro (Sxs , refl , refl)
