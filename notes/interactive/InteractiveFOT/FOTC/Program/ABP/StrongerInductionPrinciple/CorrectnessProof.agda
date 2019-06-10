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

module InteractiveFOT.FOTC.Program.ABP.StrongerInductionPrinciple.CorrectnessProof where

open import InteractiveFOT.FOTC.Relation.Binary.Bisimilarity.Type
open import InteractiveFOT.FOTC.Program.ABP.StrongerInductionPrinciple.Lemma

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Data.Stream.Type
open import Interactive.FOTC.Data.Stream.Equality.Properties
open import Interactive.FOTC.Program.ABP.ABP hiding ( B )
open import Interactive.FOTC.Program.ABP.Fair.Type
open import Interactive.FOTC.Program.ABP.Terms
open import Interactive.FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------
-- Main theorem.
abpCorrect : ∀ {b is os₁ os₂} → Bit b → Stream is → Fair os₁ → Fair os₂ →
             is ≈ abpTransfer b os₁ os₂ is
abpCorrect {b} {is} {os₁} {os₂} Bb Sis Fos₁ Fos₂ = ≈-stronger-coind B h refl
  where
  B : D → D → Set
  B xs ys = xs ≡ xs

  h : B is (abpTransfer b os₁ os₂ is) →
      ∃[ i' ] ∃[ is' ] ∃[ js' ]
        is ≡ i' ∷ is' ∧ abpTransfer b os₁ os₂ is ≡ i' ∷ js' ∧ B is' js'
  h _ with Stream-out Sis
  ... | i' , is' , prf₁ , Sis' with lemma Bb Fos₁ Fos₂ prf₂
    where
    aux₁ aux₂ aux₃ aux₄ aux₅ : D
    aux₁ = send b
    aux₂ = ack b
    aux₃ = out b
    aux₄ = corrupt os₁
    aux₅ = corrupt os₂

    prf₂ : S b (i' ∷ is') os₁ os₂
            (has aux₁ aux₂ aux₃ aux₄ aux₅ (i' ∷ is'))
            (hbs aux₁ aux₂ aux₃ aux₄ aux₅ (i' ∷ is'))
            (hcs aux₁ aux₂ aux₃ aux₄ aux₅ (i' ∷ is'))
            (hds aux₁ aux₂ aux₃ aux₄ aux₅ (i' ∷ is'))
            (abpTransfer b os₁ os₂ (i' ∷ is'))
    prf₂ = has-eq aux₁ aux₂ aux₃ aux₄ aux₅ (i' ∷ is')
           , hbs-eq aux₁ aux₂ aux₃ aux₄ aux₅ (i' ∷ is')
           , hcs-eq aux₁ aux₂ aux₃ aux₄ aux₅ (i' ∷ is')
           , hds-eq aux₁ aux₂ aux₃ aux₄ aux₅ (i' ∷ is')
           , trans (abpTransfer-eq b os₁ os₂ (i' ∷ is'))
               (transfer-eq aux₁ aux₂ aux₃ aux₄ aux₅ (i' ∷ is'))

  ... | js' , prf₃ = i'
                     , is'
                     , js'
                     , prf₁
                     , subst (λ t → abpTransfer b os₁ os₂ t ≡ i' ∷ js' )
                             (sym prf₁)
                             prf₃
                     , refl

------------------------------------------------------------------------------
-- abpTransfer produces a Stream.
abpTransfer-Stream : ∀ {b is os₁ os₂} →
                     Bit b →
                     Stream is →
                     Fair os₁ →
                     Fair os₂ →
                     Stream (abpTransfer b os₁ os₂ is)
abpTransfer-Stream Bb Sis Fos₁ Fos₂ = ≈→Stream₂ (abpCorrect Bb Sis Fos₁ Fos₂)

------------------------------------------------------------------------------
-- References
--
-- Dybjer, Peter and Sander, Herbert P. (1989). A Functional
-- Programming Approach to the Specification and Verification of
-- Concurrent Systems. Formal Aspects of Computing 1, pp. 303–319.
