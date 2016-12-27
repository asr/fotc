------------------------------------------------------------------------------
-- The alternating bit protocol (ABP) is correct
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module proves the correctness of the ABP by simplifing the
-- formalization in Dybjer and Sander (1989) using a stronger (maybe
-- invalid) co-induction principle.

module FOT.FOTC.Program.ABP.StrongerInductionPrinciple.CorrectnessProofATP
  where

open import FOT.FOTC.Relation.Binary.Bisimilarity.Type
open import FOT.FOTC.Program.ABP.StrongerInductionPrinciple.LemmaATP

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream.Type
open import FOTC.Data.Stream.Equality.PropertiesATP
open import FOTC.Program.ABP.ABP hiding ( B )
open import FOTC.Program.ABP.Fair.Type
open import FOTC.Program.ABP.Terms
open import FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------
postulate
  helper :
    ∀ b i' is' os₁ os₂ →
    S b (i' ∷ is') os₁ os₂
      (has (send b) (ack b) (out b) (corrupt os₁) (corrupt os₂) (i' ∷ is'))
      (hbs (send b) (ack b) (out b) (corrupt os₁) (corrupt os₂) (i' ∷ is'))
      (hcs (send b) (ack b) (out b) (corrupt os₁) (corrupt os₂) (i' ∷ is'))
      (hds (send b) (ack b) (out b) (corrupt os₁) (corrupt os₂) (i' ∷ is'))
      (abpTransfer b os₁ os₂ (i' ∷ is'))
{-# ATP prove helper #-}

-- Main theorem.

-- See Issue https://github.com/asr/apia/issues/81 .
abpCorrectB : D → D → Set
abpCorrectB xs ys = xs ≡ xs
{-# ATP definition abpCorrectB #-}


abpCorrect : ∀ {b is os₁ os₂} → Bit b → Stream is → Fair os₁ → Fair os₂ →
             is ≈ abpTransfer b os₁ os₂ is
abpCorrect {b} {is} {os₁} {os₂} Bb Sis Fos₁ Fos₂ = ≈-stronger-coind abpCorrectB h refl
  where
  postulate
    h : abpCorrectB is (abpTransfer b os₁ os₂ is) →
        ∃[ i' ] ∃[ is' ] ∃[ js' ]
          is ≡ i' ∷ is' ∧ abpTransfer b os₁ os₂ is ≡ i' ∷ js' ∧ abpCorrectB is' js'
  {-# ATP prove h helper lemma #-}

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
-- References
--
-- Dybjer, Peter and Sander, Herbert P. (1989). A Functional
-- Programming Approach to the Specification and Verification of
-- Concurrent Systems. Formal Aspects of Computing 1, pp. 303–319.
