------------------------------------------------------------------------------
-- ABP minor premise
------------------------------------------------------------------------------

module FOTC.Program.ABP.MinorPremiseI where

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Data.Stream.Equality
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Lemma1I
open import FOTC.Program.ABP.Lemma2I

------------------------------------------------------------------------------

-- The relation _B_ is a post-fixed point of the bisimilarity functor
-- (see FOTC.Relation.Binary.Bisimilarity). The paper calls it the
-- minor premise.

-- From the paper: The proof of the minor premise uses two lemmas. The
-- first lemma (lemma₁) states that given a start state Abp (of the
-- alternating bit protocol) we will arrive at a state Abp', where the
-- message has been received by the receiver, but where the
-- acknowledgement has not yet been received by the sender. The second
-- lemma (lemma₂) states that given a state of the latter kind we will
-- arrive at a new start state, which is identical to the old start
-- state except that the bit has alternated and the first item in the
-- input stream has been removed.

minorPremise : ∀ {is js} → is B js →
               ∃ λ i' → ∃ λ is' → ∃ λ js' →
               is' B js' ∧ is ≡ i' ∷ is' ∧ js ≡ i' ∷ js'
minorPremise {is} {js}
             (b , os₀ , os₁ , as , bs , cs , ds , Sis , Bb , Fos₀ , Fos₁ , h) =
  i' , is' , js' , is'Bjs' , is≡i'∷is , js≡i'∷js'

  where
  unfold-is : ∃ λ i' → ∃ λ is' → Stream is' ∧ is ≡ i' ∷ is'
  unfold-is = Stream-gfp₁ Sis

  i' : D
  i' = ∃-proj₁ unfold-is

  is' : D
  is' = ∃-proj₁ (∃-proj₂ unfold-is)

  Sis' : Stream is'
  Sis' = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold-is))

  is≡i'∷is : is ≡ i' ∷ is'
  is≡i'∷is = ∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-is))

  Abp-helper : is ≡ i' ∷ is' →
               Abp b is os₀ os₁ as bs cs ds js →
               Abp b (i' ∷ is') os₀ os₁ as bs cs ds js
  Abp-helper h₁ h₂ = subst (λ t → Abp b t os₀ os₁ as bs cs ds js) h₁ h₂

  Abp'-lemma₁ : ∃ λ os₀' → ∃ λ os₁' →
                ∃ λ as' → ∃ λ bs' → ∃ λ cs' → ∃ λ ds' → ∃ λ js' →
                Fair os₀'
                ∧ Fair os₁'
                ∧ Abp' b i' is' os₀' os₁' as' bs' cs' ds' js'
                ∧ js ≡ i' ∷ js'

  Abp'-lemma₁ = lemma₁ Bb Fos₀ Fos₁ (Abp-helper is≡i'∷is h)

  -- Following Martin Escardo advice (see Agda mailing list, heap
  -- mistery) we use pattern matching instead of ∃ eliminators to
  -- project the elements of the existentials. Update on 2011-08-25:
  -- It does not seems strictly necessary because the Agda issue 415
  -- was fixed.
  js' : D
  js' with Abp'-lemma₁
  ... | _ , _ , _ , _ , _ , _ , js' , _ = js'

  js≡i'∷js' : js ≡ i' ∷ js'
  js≡i'∷js' with Abp'-lemma₁
  ... | _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , h = h

  Abp-lemma₂ :  ∃ λ os₀'' → ∃ λ os₁'' →
                ∃ λ as'' → ∃ λ bs'' → ∃ λ cs'' → ∃ λ ds'' →
                Fair os₀''
                ∧ Fair os₁''
                ∧ Abp (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'
  Abp-lemma₂ with Abp'-lemma₁
  Abp-lemma₂ | _ , _ , _ , _ , _ , _ , _ , Fos₀' , Fos₁' , abp' , _ =
    lemma₂ Bb Fos₀' Fos₁' abp'

  is'Bjs' : is' B js'
  is'Bjs' with Abp-lemma₂
  ... | os₀'' , os₁'' , as'' , bs'' , cs'' , ds'' , Fos₀'' , Fos₁'' , abp =
    not b , os₀'' , os₁'' , as'' , bs'' , cs'' , ds''
    , Sis' , not-Bool Bb , Fos₀'' , Fos₁'' , abp
