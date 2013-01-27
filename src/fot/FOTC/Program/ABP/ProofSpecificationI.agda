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
open import FOTC.Base.List
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Lemma1I
open import FOTC.Program.ABP.Lemma2I
open import FOTC.Program.ABP.Terms
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------
-- Main theorem.
spec : ∀ {b is os₀ os₁} → Bit b → Stream is → Fair os₀ → Fair os₁ →
       is ≈ transfer b os₀ os₁ is
spec {b} {is} {os₀} {os₁} Bb Sis Fos₀ Fos₁ = ≈-coind B prf₁ prf₂
  where
  prf₁ : ∀ {is js} → B is js →
       ∃[ i' ] ∃[ is' ] ∃[ js' ] B is' js' ∧ is ≡ i' ∷ is' ∧ js ≡ i' ∷ js'
  prf₁ {is} {js} (b , os₀ , os₁ , as , bs , cs , ds , Sis , Bb , Fos₀ , Fos₁ , h)
     with Stream-unf Sis
  ... | (i' , is' , Sis' , is≡i'∷is) =
    i' , is' , js' , Bis'js' , is≡i'∷is , js≡i'∷js'
    where
    ABP-helper : is ≡ i' ∷ is' →
                 ABP b is os₀ os₁ as bs cs ds js →
                 ABP b (i' ∷ is') os₀ os₁ as bs cs ds js
    ABP-helper h₁ h₂ = subst (λ t → ABP b t os₀ os₁ as bs cs ds js) h₁ h₂

    ABP'-lemma₁ : ∃[ os₀' ] ∃[ os₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
                  Fair os₀'
                  ∧ Fair os₁'
                  ∧ ABP' b i' is' os₀' os₁' as' bs' cs' ds' js'
                  ∧ js ≡ i' ∷ js'
    ABP'-lemma₁ = lemma₁ Bb Fos₀ Fos₁ (ABP-helper is≡i'∷is h)

    -- Following Martin Escardo advice (see Agda mailing list, heap
    -- mistery) we use pattern matching instead of ∃ eliminators to
    -- project the elements of the existentials.

    -- 2011-08-25 update: It does not seems strictly necessary because
    -- the Agda issue 415 was fixed.

    js' : D
    js' with ABP'-lemma₁
    ... | _ , _ , _ , _ , _ , _ , js' , _ = js'

    js≡i'∷js' : js ≡ i' ∷ js'
    js≡i'∷js' with ABP'-lemma₁
    ... | _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , h = h

    ABP-lemma₂ : ∃[ os₀'' ] ∃[ os₁'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
                 Fair os₀''
                 ∧ Fair os₁''
                 ∧ ABP (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'
    ABP-lemma₂ with ABP'-lemma₁
    ABP-lemma₂ | _ , _ , _ , _ , _ , _ , _ , Fos₀' , Fos₁' , abp' , _ =
      lemma₂ Bb Fos₀' Fos₁' abp'

    Bis'js' : B is' js'
    Bis'js' with ABP-lemma₂
    ... | os₀'' , os₁'' , as'' , bs'' , cs'' , ds'' , Fos₀'' , Fos₁'' , abp =
      not b , os₀'' , os₁'' , as'' , bs'' , cs'' , ds''
      , Sis' , not-Bool Bb , Fos₀'' , Fos₁'' , abp

  prf₂ : B is (transfer b os₀ os₁ is)
  prf₂ = b
       , os₀
       , os₁
       , has (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
       , hbs (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
       , hcs (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
       , hds (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
       , Sis
       , Bb
       , Fos₀
       , Fos₁
       , has-eq (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
       , hbs-eq (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
       , hcs-eq (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
       , hds-eq (send · b) (ack · b) (out · b) (corrupt · os₀) (corrupt · os₁) is
       , trans (transfer-eq b os₀ os₁ is)
               (genTransfer-eq (send · b) (ack · b) (out · b) (corrupt · os₀)
                               (corrupt · os₁) is)
