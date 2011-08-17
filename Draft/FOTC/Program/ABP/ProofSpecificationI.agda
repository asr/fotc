------------------------------------------------------------------------------
-- The alternating bit protocol (ABP) satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the ABP following the
-- formalization in [1].

-- [1] Peter Dybjer and Herbert Sander. A functional programming
--     approach to the specification and verification of concurrent
--     systems. Formal Aspects of Computing, 1:303–319, 1989.

module Draft.FOTC.Program.ABP.ProofSpecificationI where

open import FOTC.Base

open import FOTC.Data.Stream.Type

open import FOTC.Relation.Binary.Bisimilarity

open import Draft.FOTC.Program.ABP.ABP
open import Draft.FOTC.Program.ABP.Fair
open import Draft.FOTC.Program.ABP.MayorPremiseI
open import Draft.FOTC.Program.ABP.MinorPremiseI
open import Draft.FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Main theorem.
spec : ∀ {b is os₀ os₁} → Bit b → Stream is → Fair os₀ → Fair os₁ →
       is ≈ transfer (abpsend · b)
                     (abpack · b)
                     (abpout · b)
                     (corrupt · os₀)
                     (corrupt · os₁)
                     is
spec {b} {is} {os₀} {os₁} Bb Sis Fos₀ Fos₁ =
  subst (_≈_ is)
        (abptrans-eq b os₀ os₁ is)
        (≈-gfp₂ _B_ minorPremise (mayorPremise Bb Fos₀ Fos₁ Sis))
