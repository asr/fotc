------------------------------------------------------------------------------
-- The alternating bit protocol (ABP) is correct
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module proves the correctness of the ABP following the
-- formalization in Dybjer and Sander (1989).

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module Combined.FOTC.Program.ABP.CorrectnessProof where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.Bool
open import Combined.FOTC.Data.Bool.Properties using ( not-Bool )
open import Combined.FOTC.Data.Stream.Type
open import Combined.FOTC.Data.Stream.Equality.Properties
open import Combined.FOTC.Program.ABP.ABP
open import Combined.FOTC.Program.ABP.Lemma1
open import Combined.FOTC.Program.ABP.Lemma2
open import Combined.FOTC.Program.ABP.Fair.Type
open import Combined.FOTC.Program.ABP.Terms
open import Combined.FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------
-- Main theorem.
abpCorrect : ∀ {b os₁ os₂ is} → Bit b → Fair os₁ → Fair os₂ → Stream is →
             is ≈ abpTransfer b os₁ os₂ is
abpCorrect {b} {os₁} {os₂} {is} Bb Fos₁ Fos₂ Sis = ≈-coind B h₁ h₂
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
  abpTransfer-Stream : ∀ {b os₁ os₂ is} →
                       Bit b →
                       Fair os₁ →
                       Fair os₂ →
                       Stream is →
                       Stream (abpTransfer b os₁ os₂ is)
{-# ATP prove abpTransfer-Stream ≈→Stream₂ abpCorrect #-}

------------------------------------------------------------------------------
-- References
--
-- Dybjer, Peter and Sander, Herbert P. (1989). A Functional
-- Programming Approach to the Specification and Verification of
-- Concurrent Systems. Formal Aspects of Computing 1, pp. 303–319.
