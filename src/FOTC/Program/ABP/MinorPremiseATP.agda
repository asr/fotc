------------------------------------------------------------------------------
-- ABP minor premise
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOTC.Program.ABP.MinorPremiseATP where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Stream
open import FOTC.Data.Stream.Equality
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Lemma1ATP
open import FOTC.Program.ABP.Lemma2ATP

------------------------------------------------------------------------------

-- The relation _B_ is a post-fixed point of the bisimilarity functor
-- (see FOTC.Relation.Binary.Bisimilarity). The paper calls it the
-- minor premise.

-- From Dybjer and Sander's paper: The proof of the minor premise uses
-- two lemmas. The first lemma (lemma₁) states that given a start
-- state Abp (of the alternating bit protocol) we will arrive at a
-- state Abp', where the message has been received by the receiver,
-- but where the acknowledgement has not yet been received by the
-- sender. The second lemma (lemma₂) states that given a state of the
-- latter kind we will arrive at a new start state, which is identical
-- to the old start state except that the bit has alternated and the
-- first item in the input stream has been removed.

minorPremise : ∀ {is js} → is B js →
               ∃[ i' ] ∃[ is' ] ∃[ js' ]
               is' B js' ∧ is ≡ i' ∷ is' ∧ js ≡ i' ∷ js'
minorPremise
  {is} {js}
  (b , fs₀ , fs₁ , as , bs , cs , ds , Sis , Bb , Ffs₀ , Ffs₁ , h)
  with (Stream-gfp₁ Sis)
... | (i' , is' , Sis' , is≡i'∷is) = i' , is' , js' , is'Bjs' , is≡i'∷is , js≡i'∷js'

  where
  Abp-helper : is ≡ i' ∷ is' →
               Abp b is fs₀ fs₁ as bs cs ds js →
               Abp b (i' ∷ is') fs₀ fs₁ as bs cs ds js
  Abp-helper h₁ h₂ = subst (λ t → Abp b t fs₀ fs₁ as bs cs ds js) h₁ h₂

  Abp'-lemma₁ : ∃[ fs₀' ] ∃[ fs₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
                Fair fs₀'
                ∧ Fair fs₁'
                ∧ Abp' b i' is' fs₀' fs₁' as' bs' cs' ds' js'
                ∧ js ≡ i' ∷ js'
  Abp'-lemma₁ = lemma₁ Bb Ffs₀ Ffs₁ (Abp-helper is≡i'∷is h)

  -- Following Martin Escardo advice (see Agda mailing list, heap
  -- mistery) we use pattern matching instead of ∃ eliminators to
  -- project the elements of the existentials.

  -- 2011-08-25 update: It does not seems strictly necessary because
  -- the Agda issue 415 was fixed.

  js' : D
  js' with Abp'-lemma₁
  ... | _ , _ , _ , _ , _ , _ , js' , _ = js'

  js≡i'∷js' : js ≡ i' ∷ js'
  js≡i'∷js' with Abp'-lemma₁
  ... | _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , h = h

  Abp-lemma₂ : ∃[ fs₀'' ] ∃[ fs₁'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
               Fair fs₀''
               ∧ Fair fs₁''
               ∧ Abp (not b) is' fs₀'' fs₁'' as'' bs'' cs'' ds'' js'
  Abp-lemma₂ with Abp'-lemma₁
  Abp-lemma₂ | _ , _ , _ , _ , _ , _ , _ , Ffs₀' , Ffs₁' , abp' , _ =
    lemma₂ Bb Ffs₀' Ffs₁' abp'

  is'Bjs' : is' B js'
  is'Bjs' with Abp-lemma₂
  ... | fs₀'' , fs₁'' , as'' , bs'' , cs'' , ds'' , Ffs₀'' , Ffs₁'' , abp =
    not b , fs₀'' , fs₁'' , as'' , bs'' , cs'' , ds''
    , Sis' , not-Bool Bb , Ffs₀'' , Ffs₁'' , abp
