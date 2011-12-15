------------------------------------------------------------------------------
-- The alternating bit protocol (ABP) satisfies the specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the ABP following the
-- formalization in [1].

-- [1] Peter Dybjer and Herbert Sander. A functional programming
--     approach to the specification and verification of concurrent
--     systems. Formal Aspects of Computing, 1:303–319, 1989.

module FOTC.Program.ABP.ProofSpecificationI where

open import FOTC.Base
open import FOTC.Data.Stream
open import FOTC.Data.Stream.Equality
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.MayorPremiseI
open import FOTC.Program.ABP.MinorPremiseI
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Main theorem.
spec : ∀ {b is os₀ os₁} → Bit b → Stream is → Fair os₀ → Fair os₁ →
       is ≈ abptransfer b os₀ os₁ is
spec {b} {is} {os₀} {os₁} Bb Sis Fos₀ Fos₁ =
  ≈-gfp₂ _B_ minorPremise (mayorPremise Bb Fos₀ Fos₁ Sis)
