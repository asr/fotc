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

-- Main theorem
spec : ∀ {b is os₀ os₁} → Bit b → Stream is → Fair os₀ → Fair os₁ →
       is ≈ transfer (abpsend b)
                     (abpack b)
                     (abpout b)
                     (corrupt os₀)
                     (corrupt os₁)
                     is
spec {b} {is} {os₀} {os₁} Bb Sis Fos₀ Fos₁ =
  subst (_≈_ is)
        (abptrans-eq b os₀ os₁ is)
        (≈-gfp₂ _B_ minorPremise (mayorPremise Bb Fos₀ Fos₁ Sis))
