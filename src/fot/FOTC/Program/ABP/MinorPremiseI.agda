------------------------------------------------------------------------------
-- ABP minor premise
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.MinorPremiseI where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Lemma1I
open import FOTC.Program.ABP.Lemma2I
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

-- The relation B is a post-fixed point of the bisimilarity functional
-- (see FOTC.Relation.Binary.Bisimilarity). The paper calls it the
-- minor premise.

-- From Dybjer and Sander's paper: The proof of the minor premise uses
-- two lemmas. The first lemma (lemma₁) states that given a start
-- state ABP (of the alternating bit protocol) we will arrive at a
-- state ABP', where the message has been received by the receiver,
-- but where the acknowledgement has not yet been received by the
-- sender. The second lemma (lemma₂) states that given a state of the
-- latter kind we will arrive at a new start state, which is identical
-- to the old start state except that the bit has alternated and the
-- first item in the input stream has been removed.

minorPremise : ∀ {is js} → B is js →
               ∃[ i' ] ∃[ is' ] ∃[ js' ]
               B is' js' ∧ is ≡ i' ∷ is' ∧ js ≡ i' ∷ js'
minorPremise
  {is} {js}
  (b , os₀ , os₁ , as , bs , cs , ds , Sis , Bb , Fos₀ , Fos₁ , h)
  with (Stream-unf Sis)
... | (i' , is' , Sis' , is≡i'∷is) = i' , is' , js' , Bis'js' , is≡i'∷is , js≡i'∷js'

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
