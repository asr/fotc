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

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.ABP.ProofSpecificationATP where

open import FOTC.Base
open import FOTC.Data.Stream
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.MayorPremiseATP
open import FOTC.Program.ABP.MinorPremiseATP
open import FOTC.Program.ABP.Terms
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

-- Main theorem.
spec : ∀ {b is fs₀ fs₁} → Bit b → Stream is → Fair fs₀ → Fair fs₁ →
       is ≈ abptransfer b fs₀ fs₁ is
spec Bb Sis Ffs₀ Ffs₁ = ≈-gfp₂ _B_ minorPremise (mayorPremise Bb Ffs₀ Ffs₁ Sis)
