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

module FOTC.Program.ABP.ProofSpecification.UnprovedATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Stream
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Lemma1ATP
open import FOTC.Program.ABP.Lemma2ATP
open import FOTC.Program.ABP.Terms
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------
-- Main theorem.
spec : ∀ {b is os₀ os₁} → Bit b → Stream is → Fair os₀ → Fair os₁ →
       is ≈ transfer b os₀ os₁ is
spec {b} {is} {os₀} {os₁} Bb Sis Fos₀ Fos₁ = ≈-coind B prf₁ prf₂
  where
  postulate prf₁ : ∀ {is js} → B is js →
                   ∃[ i' ] ∃[ is' ] ∃[ js' ]
                   is ≡ i' ∷ is' ∧ js ≡ i' ∷ js' ∧ B is' js'
  {-# ATP prove prf₁ lemma₁ lemma₂ not-Bool #-}

  -- 17 December 2012: The ATPs could not prove the theorem (240 sec).
  postulate prf₂ : B is (transfer b os₀ os₁ is)
  {-# ATP prove prf₂ #-}
