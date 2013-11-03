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

module FOTC.Program.ABP.SpecificationProofI where

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
spec : ∀ {b is os₁ os₂} → Bit b → Stream is → Fair os₁ → Fair os₂ →
       is ≈ abpTransfer b os₁ os₂ is
spec {b} {is} {os₁} {os₂} Bb Sis Fos₁ Fos₂ = ≈-coind B prf₁ prf₂
  where
  prf₁ : ∀ {is js} → B is js →
         ∃[ i' ] ∃[ is' ] ∃[ js' ] is ≡ i' ∷ is' ∧ js ≡ i' ∷ js' ∧ B is' js'
  prf₁ {is} {js} (b , os₁ , os₂ , as , bs , cs , ds , Sis , Bb , Fos₁ , Fos₂ , h)
     with Stream-unf Sis
  ... | (i' , is' , is≡i'∷is , Sis') =
    i' , is' , js' , is≡i'∷is , js≡i'∷js' , Bis'js'
    where
    State-helper : is ≡ i' ∷ is' →
                   State b is os₁ os₂ as bs cs ds js →
                   State b (i' ∷ is') os₁ os₂ as bs cs ds js
    State-helper h₁ h₂ = subst (λ t → State b t os₁ os₂ as bs cs ds js) h₁ h₂

    State'-lemma₁ : ∃[ os₁' ] ∃[ os₂' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
                    Fair os₁'
                    ∧ Fair os₂'
                    ∧ State' b i' is' os₁' os₂' as' bs' cs' ds' js'
                    ∧ js ≡ i' ∷ js'
    State'-lemma₁ = lemma₁ Bb Fos₁ Fos₂ (State-helper is≡i'∷is h)

    -- Following Martin Escardo advice (see Agda mailing list, heap
    -- mistery) we use pattern matching instead of ∃ eliminators to
    -- project the elements of the existentials.

    -- 2011-08-25 update: It does not seems strictly necessary because
    -- the Agda issue 415 was fixed.

    js' : D
    js' with State'-lemma₁
    ... | _ , _ , _ , _ , _ , _ , js' , _ = js'

    js≡i'∷js' : js ≡ i' ∷ js'
    js≡i'∷js' with State'-lemma₁
    ... | _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , h = h

    State-lemma₂ : ∃[ os₁'' ] ∃[ os₂'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
                   Fair os₁''
                   ∧ Fair os₂''
                   ∧ State (not b) is' os₁'' os₂'' as'' bs'' cs'' ds'' js'
    State-lemma₂ with State'-lemma₁
    ... | _ , _ , _ , _ , _ , _ , _ , Fos₁' , Fos₂' , state' , _ =
      lemma₂ Bb Fos₁' Fos₂' state'

    Bis'js' : B is' js'
    Bis'js' with State-lemma₂
    ... | os₁'' , os₂'' , as'' , bs'' , cs'' , ds'' , Fos₁'' , Fos₂'' , state =
      not b , os₁'' , os₂'' , as'' , bs'' , cs'' , ds''
      , Sis' , not-Bool Bb , Fos₁'' , Fos₂'' , state

  prf₂ : B is (abpTransfer b os₁ os₂ is)
  prf₂ = b
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
