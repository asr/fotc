------------------------------------------------------------------------------
-- The alternating bit protocol (ABP) satisfies the specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the ABP following the
-- formalization in Dybjer and Sander (1989).
--
-- References:
--
-- • Dybjer, Peter and Sander, Herbert P. (1989). A Functional
--   Programming Approach to the Speciﬁcation and Veriﬁcation of
--   Concurrent Systems. In: Formal Aspects of Computing 1,
--   pp. 303–319.
--
-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.ABP.ProofSpecificationATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesATP using ( not-Bool )
open import FOTC.Data.Stream
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Lemma1ATP
open import FOTC.Program.ABP.Lemma2ATP
open import FOTC.Program.ABP.Terms
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------
-- Main theorem.
spec : ∀ {b is os₁ os₂} → Bit b → Stream is → Fair os₁ → Fair os₂ →
       is ≈ abpTransfer b os₁ os₂ is
spec {b} {is} {os₁} {os₂} Bb Sis Fos₁ Fos₂ = ≈-coind B prf₁ prf₂
  where
  postulate prf₁ : ∀ {is js} → B is js →
                   ∃[ i' ] ∃[ is' ] ∃[ js' ]
                   is ≡ i' ∷ is' ∧ js ≡ i' ∷ js' ∧ B is' js'
  {-# ATP prove prf₁ lemma₁ lemma₂ not-Bool #-}

  postulate prf₂ : B is (abpTransfer b os₁ os₂ is)
  {-# ATP prove prf₂ #-}
