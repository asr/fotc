------------------------------------------------------------------------------
-- The alternating bit protocol (ABP) is correct
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the ABP following the
-- formalization in Dybjer and Sander (1989).

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.ABP.DS.CorrectnessProofATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesATP using ( not-Bool )
open import FOTC.Data.Stream
open import FOTC.Data.Stream.Equality.PropertiesATP
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.DS.ABP
open import FOTC.Program.ABP.DS.Lemma1I
open import FOTC.Program.ABP.DS.Lemma2I
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Terms
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------
-- Main theorem.
abpCorrect : ∀ {b is os₁ os₂} → Bit b → Stream is → Fair os₁ → Fair os₂ →
             is ≈ abpTransfer b os₁ os₂ is
abpCorrect {b} {is} {os₁} {os₂} Bb Sis Fos₁ Fos₂ = ≈-coind B h₁ h₂
  where
  postulate h₁ : ∀ {ks ls} → B ks ls →
                 ∃[ k' ] ∃[ ks' ] ∃[ ls' ]
                   ks ≡ k' ∷ ks' ∧ ls ≡ k' ∷ ls' ∧ B ks' ls'
  {-# ATP prove h₁ lemma₁ lemma₂ not-Bool #-}

  postulate h₂ : B is (abpTransfer b os₁ os₂ is)
  {-# ATP prove h₂ #-}

------------------------------------------------------------------------------
-- abpTransfer produces a Stream.
postulate
  abpTransfer-Stream : ∀ {b is os₁ os₂} →
                       Bit b →
                       Stream is →
                       Fair os₁ →
                       Fair os₂ →
                       Stream (abpTransfer b os₁ os₂ is)
{-# ATP prove abpTransfer-Stream ≈→Stream₂ abpCorrect #-}

------------------------------------------------------------------------------
-- References:
--
-- • Dybjer, Peter and Sander, Herbert P. (1989). A Functional
--   Programming Approach to the Speciﬁcation and Veriﬁcation of
--   Concurrent Systems. In: Formal Aspects of Computing 1,
--   pp. 303–319.
