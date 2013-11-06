------------------------------------------------------------------------------
-- The alternating bit protocol (ABP) is correct
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

module FOTC.Program.ABP.CorrectnessProofI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Data.Stream.Equality.PropertiesI
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Lemma1I
open import FOTC.Program.ABP.Lemma2I
open import FOTC.Program.ABP.Terms
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------
-- Main theorem.
abpCorrect : ∀ {b is os₁ os₂} → Bit b → Stream is → Fair os₁ → Fair os₂ →
             is ≈ abpTransfer b os₁ os₂ is
abpCorrect {b} {is} {os₁} {os₂} Bb Sis Fos₁ Fos₂ = ≈-coind B h₁ h₂
  where
  h₁ : ∀ {ks ls} → B ks ls →
       ∃[ k' ] ∃[ ks' ] ∃[ ls' ] ks ≡ k' ∷ ks' ∧ ls ≡ k' ∷ ls' ∧ B ks' ls'
  h₁ {ks} {ls} (b , os₁ , os₂ , as , bs , cs , ds , Sks , Bb , Fos₁ , Fos₂ , h)
     with Stream-unf Sks
  ... | (k' , ks' , ks≡k'∷ks' , Sks') =
    k' , ks' , ls' , ks≡k'∷ks' , ls≡k'∷ls' , Bks'ls'
    where
    S-helper : ks ≡ k' ∷ ks' →
               S b ks os₁ os₂ as bs cs ds ls →
               S b (k' ∷ ks') os₁ os₂ as bs cs ds ls
    S-helper h₁ h₂ = subst (λ t → S b t os₁ os₂ as bs cs ds ls) h₁ h₂

    S'-lemma₁ : ∃[ os₁' ] ∃[ os₂' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ ls' ]
                  Fair os₁'
                  ∧ Fair os₂'
                  ∧ S' b k' ks' os₁' os₂' as' bs' cs' ds' ls'
                  ∧ ls ≡ k' ∷ ls'
    S'-lemma₁ = lemma₁ Bb Fos₁ Fos₂ (S-helper ks≡k'∷ks' h)

    -- Following Martin Escardo advice (see Agda mailing list, heap
    -- mistery) we use pattern matching instead of ∃ eliminators to
    -- project the elements of the existentials.

    -- 2011-08-25 update: It does not seems strictly necessary because
    -- the Agda issue 415 was fixed.

    ls' : D
    ls' with S'-lemma₁
    ... | _ , _ , _ , _ , _ , _ , ls' , _ = ls'

    ls≡k'∷ls' : ls ≡ k' ∷ ls'
    ls≡k'∷ls' with S'-lemma₁
    ... | _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , h = h

    S-lemma₂ : ∃[ os₁'' ] ∃[ os₂'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
                 Fair os₁''
                 ∧ Fair os₂''
                 ∧ S (not b) ks' os₁'' os₂'' as'' bs'' cs'' ds'' ls'
    S-lemma₂ with S'-lemma₁
    ... | _ , _ , _ , _ , _ , _ , _ , Fos₁' , Fos₂' , s' , _ =
      lemma₂ Bb Fos₁' Fos₂' s'

    Bks'ls' : B ks' ls'
    Bks'ls' with S-lemma₂
    ... | os₁'' , os₂'' , as'' , bs'' , cs'' , ds'' , Fos₁'' , Fos₂'' , s =
      not b , os₁'' , os₂'' , as'' , bs'' , cs'' , ds''
      , Sks' , not-Bool Bb , Fos₁'' , Fos₂'' , s

  h₂ : B is (abpTransfer b os₁ os₂ is)
  h₂ = b
       , os₁
       , os₂
       , has a₁ a₂ a₃ a₄ a₅ is
       , hbs a₁ a₂ a₃ a₄ a₅ is
       , hcs a₁ a₂ a₃ a₄ a₅ is
       , hds a₁ a₂ a₃ a₄ a₅ is
       , Sis
       , Bb
       , Fos₁
       , Fos₂
       , has-eq a₁ a₂ a₃ a₄ a₅ is
       , hbs-eq a₁ a₂ a₃ a₄ a₅ is
       , hcs-eq a₁ a₂ a₃ a₄ a₅ is
       , hds-eq a₁ a₂ a₃ a₄ a₅ is
       , trans (abpTransfer-eq b os₁ os₂ is) (transfer-eq a₁ a₂ a₃ a₄ a₅ is)
    where
    a₁ a₂ a₃ a₄ a₅ : D
    a₁ = send b
    a₂ = ack b
    a₃ = out b
    a₄ = corrupt os₁
    a₅ = corrupt os₂

abp-Stream : ∀ {b is os₁ os₂} → Bit b → Stream is → Fair os₁ → Fair os₂ →
             Stream (abpTransfer b os₁ os₂ is)
abp-Stream Bb Sis Fos₁ Fos₂ = ≈→Stream₂ (abpCorrect Bb Sis Fos₁ Fos₂)
