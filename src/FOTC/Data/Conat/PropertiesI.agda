------------------------------------------------------------------------------
-- Conat properties
------------------------------------------------------------------------------

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

  helper : {n : D} → P n → ∃ (λ n' → P n' ∧ n ≡ succ₁ n')
  helper Pn = ω , refl , trans Pn ω-eq

-- Adapted from Herbert's thesis, p. 58.
stream-length : ∀ {xs} → Stream xs → length xs ≈N ω
stream-length {xs} Sxs = ≈N-gfp₂ _R_ helper₁ helper₂
  where
  _R_ : D → D → Set
  m R n = ∃ λ ys → Stream ys ∧ m ≡ length ys ∧ n ≡ ω

  helper₁ : ∀ {m n} → m R n →
            ∃ λ m' → ∃ λ n' → m' R n' ∧ m ≡ succ₁ m' ∧ n ≡ succ₁ n'
  helper₁ {m} {n} (ys , Sys , h₁ , h₂) =
    length ys' , n , (ys' , Sys' , refl , h₂) , prf₁ , prf₂
    where
    unfold-ys : ∃ λ y' → ∃ λ ys' → Stream ys' ∧ ys ≡ y' ∷ ys'
    unfold-ys = Stream-gfp₁ Sys

    y' : D
    y' = ∃-proj₁ unfold-ys

    ys' : D
    ys' = ∃-proj₁ (∃-proj₂ unfold-ys)

    Sys' : Stream ys'
    Sys' = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold-ys))

    ys≡y'∷ys' : ys ≡ y' ∷ ys'
    ys≡y'∷ys' = ∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-ys))

    prf₁ : m ≡ succ₁ (length ys')
    prf₁ = trans₂ h₁ (cong length ys≡y'∷ys') (length-∷ y' ys')

    prf₂ : n ≡ succ₁ n
    prf₂ = trans₂ h₂ ω-eq (cong succ₁ (sym h₂))

  helper₂ : length xs R ω
  helper₂ = xs , Sxs , refl , refl
