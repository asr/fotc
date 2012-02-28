------------------------------------------------------------------------------
-- ABP minor premise
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.MinorPremiseI where

open import Common.Function

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
-- 2012-02-28. We required the existential witness on a pattern matching.
minorPremise {is} {js}
 (∃-intro {b}
   (∃-intro {fs₀}
     (∃-intro {fs₁}
       (∃-intro {as}
         (∃-intro {bs}
           (∃-intro {cs}
             (∃-intro {ds}
               (Sis , Bb , Ffs₀ , Ffs₁ , h)))))))) with (Stream-gfp₁ Sis)
... | (∃-intro {i'} (∃-intro {is'} (Sis' , is≡i'∷is))) =
  ∃-intro $ ∃-intro $ ∃-intro $ is'Bjs' , is≡i'∷is , js≡i'∷js'

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

  -- 2012-02-28. We required the existential witness on a pattern matching.
  js' : D
  js' with Abp'-lemma₁
  ... | ∃-intro
          (∃-intro
            (∃-intro (∃-intro (∃-intro (∃-intro (∃-intro {js'} _)))))) = js'

  js≡i'∷js' : js ≡ i' ∷ js'
  js≡i'∷js' with Abp'-lemma₁
  ... | ∃-intro
          (∃-intro
            (∃-intro
              (∃-intro (∃-intro (∃-intro (∃-intro (_ , _ , _ , h))))))) = h

  Abp-lemma₂ : ∃[ fs₀'' ] ∃[ fs₁'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
               Fair fs₀''
               ∧ Fair fs₁''
               ∧ Abp (not b) is' fs₀'' fs₁'' as'' bs'' cs'' ds'' js'
  Abp-lemma₂ with Abp'-lemma₁
  ... | ∃-intro
          (∃-intro
            (∃-intro
              (∃-intro
                (∃-intro (∃-intro (∃-intro (Ffs₀' , Ffs₁' , abp' , _))))))) =
    lemma₂ Bb Ffs₀' Ffs₁' abp'

  is'Bjs' : is' B js'
  is'Bjs' with Abp-lemma₂
  ... | ∃-intro
          (∃-intro
            (∃-intro (∃-intro (∃-intro (∃-intro (Ffs₀'' , Ffs₁'' , abp)))))) =
    ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $
      Sis' , not-Bool Bb , Ffs₀'' , Ffs₁'' , abp
