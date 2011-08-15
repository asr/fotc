module Draft.FOTC.Program.ABP.ProofSpecification where

open import FOTC.Base

open import FOTC.Data.Stream.Type

open import FOTC.Relation.Binary.Bisimilarity

open import Draft.FOTC.Program.ABP.ABP
open import Draft.FOTC.Program.ABP.Fair
open import Draft.FOTC.Program.ABP.MayorPremise
open import Draft.FOTC.Program.ABP.MinorPremise
open import Draft.FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

Protocol : (D → D → D) → (D → D) → (D → D) → Set
Protocol f₁ f₂ f₃ = ∀ {g₁ g₂} → Futc g₁ → Futc g₂ →
                    ∀ {is} → Stream is →
                    is ≈ transfer f₁ f₂ f₃ g₁ g₂ is

spec-helper₂ : ∀ {b os₀ os₁ is} →
               Bit b → Fair os₀ → Fair os₁ → Stream is →
               is ≈ abptrans b os₀ os₁ is
spec-helper₂ Bb Fos₀ Fos₁ Sis =
  ≈-gfp₂ _B_ minorPremise (mayorPremise Bb Fos₀ Fos₁ Sis)

spec-helper : ∀ {b} → Bit b →
              ∀ {g₁ g₂} → Futc g₁ → Futc g₂ →
              ∀ {is} → Stream is →
              is ≈ transfer (abpsend b) (abpack b) (abpout b) g₁ g₂ is
spec-helper {b} Bb (os₀ , Fos₀ , g₁-eq) (os₁ , Fos₁ , g₂-eq) {is} Sis =
  subst²₂ (λ t₁ t₂ → is ≈ transfer (abpsend b) (abpack b) (abpout b) t₁ t₂ is)
          (sym² g₁-eq)
          (sym² g₂-eq)
          (subst (λ t → is ≈ t)
                 (abptrans-eq b os₀ os₁ is)
                 (spec-helper₂ Bb Fos₀ Fos₁ Sis) )

-- Main theorem
spec : ∀ {b} → Bit b → Protocol (abpsend b) (abpack b) (abpout b)
spec = spec-helper
