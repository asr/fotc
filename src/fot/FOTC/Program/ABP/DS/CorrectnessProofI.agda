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

module FOTC.Program.ABP.DS.CorrectnessProofI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Data.Stream.Equality.PropertiesI
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
    ... | _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , prf = prf

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
       , has aux₁ aux₂ aux₃ aux₄ aux₅ is
       , hbs aux₁ aux₂ aux₃ aux₄ aux₅ is
       , hcs aux₁ aux₂ aux₃ aux₄ aux₅ is
       , hds aux₁ aux₂ aux₃ aux₄ aux₅ is
       , Sis
       , Bb
       , Fos₁
       , Fos₂
       , has-eq aux₁ aux₂ aux₃ aux₄ aux₅ is
       , hbs-eq aux₁ aux₂ aux₃ aux₄ aux₅ is
       , hcs-eq aux₁ aux₂ aux₃ aux₄ aux₅ is
       , hds-eq aux₁ aux₂ aux₃ aux₄ aux₅ is
       , trans (abpTransfer-eq b os₁ os₂ is)
           (transfer-eq aux₁ aux₂ aux₃ aux₄ aux₅ is)
    where
    aux₁ aux₂ aux₃ aux₄ aux₅ : D
    aux₁ = send b
    aux₂ = ack b
    aux₃ = out b
    aux₄ = corrupt os₁
    aux₅ = corrupt os₂

------------------------------------------------------------------------------
-- abpTransfer produces a Stream.
abp-Stream : ∀ {b is os₁ os₂} → Bit b → Stream is → Fair os₁ → Fair os₂ →
             Stream (abpTransfer b os₁ os₂ is)
abp-Stream Bb Sis Fos₁ Fos₂ = ≈→Stream₂ (abpCorrect Bb Sis Fos₁ Fos₂)
