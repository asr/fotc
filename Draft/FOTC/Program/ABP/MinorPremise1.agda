------------------------------------------------------------------------------
-- ABP minor premise
------------------------------------------------------------------------------

module Draft.FOTC.Program.ABP.MinorPremise1 where

open import FOTC.Base

open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Stream.Type

open import FOTC.Relation.Binary.Bisimilarity
open import FOTC.Relation.Binary.EqReasoning

open import Draft.FOTC.Program.ABP.ABP
open import Draft.FOTC.Program.ABP.Fair
open import Draft.FOTC.Program.ABP.Lemma1
open import Draft.FOTC.Program.ABP.Lemma2

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

  P₁ : Set
  P₁ = ∃ λ os₀' → ∃ λ os₁' →
       ∃ λ as' → ∃ λ bs' → ∃ λ cs' → ∃ λ ds' → ∃ λ js' →
       Abp' b i' is' os₀' os₁' as' bs' cs' ds' js'
       ∧ js ≡ i' ∷ js'

  Abp-helper : is ≡ i' ∷ is' →
               Abp b is os₀ os₁ as bs cs ds js →
               Abp b (i' ∷ is') os₀ os₁ as bs cs ds js
  Abp-helper h₁ h₂ = subst (λ t → Abp b t os₀ os₁ as bs cs ds js) h₁ h₂

  Abp'-lemma₁ : P₁
  Abp'-lemma₁ = lemma₁ Bb Fos₀ ? (Abp-helper is≡i'∷is h)

  os₀' : D
  os₀' = ∃-proj₁ Abp'-lemma₁

  os₁' : D
  os₁' = ∃-proj₁ (∃-proj₂ Abp'-lemma₁)

  -- Following Martin Escardo advice (see Agda mailing list, heap
  -- mistery) we use pattern matching instead of ∃ eliminators to
  -- project the elements of the existentials.

  as'-helper : P₁ → D
  as'-helper (_ , _ , as' , _) = as'

  as' : D
  as' = as'-helper Abp'-lemma₁

  bs'-helper : P₁ → D
  bs'-helper (_ , _ , _ , bs' , _) = bs'

  bs' : D
  bs' = bs'-helper Abp'-lemma₁

  cs'-helper : P₁ → D
  cs'-helper (_ , _ , _ , _ , cs' , _) = cs'

  cs' : D
  cs' = cs'-helper Abp'-lemma₁

  ds'-helper : P₁ → D
  ds'-helper (_ , _ , _ , _ , _ , ds' , _) = ds'

  ds' : D
  ds' = ds'-helper Abp'-lemma₁

  js'-helper : P₁ → D
  js'-helper (_ , _ , _ , _ , _ , _ , js' , _) = js'

  js' : D
  js' = js'-helper Abp'-lemma₁

  abp'-helper : P₁ → Abp' b i' is' os₀' os₁' as' bs' cs' ds' js'
  abp'-helper (os₀' , os₁'
              , as' , bs' , cs' , ds' , js'
              , (h₁ , h₂ , h₃ , h₄ , h₅) , _) =
              subst₃ (λ x y z → x ≡ corrupt y (b ∷ z)) _ _ _ h₁
              , subst₂ (λ x y → x ≡
                           await b (∃-proj₁ (Stream-gfp₁ Sis))
                           (∃-proj₁ (∃-proj₂ (Stream-gfp₁ Sis))) y)
                        _
                        _
                        h₂
              , subst₃ (λ x y z → x ≡ corrupt y z) _ _ _ h₃
              , subst₂ (λ x y → x ≡ abpack (not b) y) _ _ h₄
              , subst₂ (λ x y → x ≡ abpout (not b) y) _ _ h₅

  abp' : Abp' b i' is' os₀' os₁' as' bs' cs' ds' js'
  abp' = abp'-helper Abp'-lemma₁

  js≡i'∷js'-helper : P₁ → js ≡ i' ∷ js'
  js≡i'∷js'-helper (_ , _ , _ , _ , _ , _ , js' , _ , h) =
                   subst (λ x → js ≡ ∃-proj₁ (Stream-gfp₁ Sis) ∷ x)
                         _
                         h

  js≡i'∷js' : js ≡ i' ∷ js'
  js≡i'∷js' = js≡i'∷js'-helper Abp'-lemma₁

  P₂ : Set
  P₂ = ∃ λ os₀'' → ∃ λ os₁'' →
       ∃ λ as'' → ∃ λ bs'' → ∃ λ cs'' → ∃ λ ds'' →
       Abp (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'

  Abp-lemma₂ : P₂
  Abp-lemma₂ = lemma₂ ? ? abp'

  os₀'' : D
  os₀'' = ∃-proj₁ Abp-lemma₂

  os₁'' : D
  os₁'' = ∃-proj₁ (∃-proj₂ Abp-lemma₂)

  as''-helper : P₂ → D
  as''-helper (_ , _ , as'' , _) = as''

  as'' : D
  as'' = as''-helper Abp-lemma₂

  bs''-helper : P₂ → D
  bs''-helper (_ , _ , _ , bs'' , _) = bs''

  bs'' : D
  bs'' = bs''-helper Abp-lemma₂

  cs''-helper : P₂ → D
  cs''-helper (_ , _ , _ , _ , cs'' , _) = cs''

  cs'' : D
  cs'' = cs''-helper Abp-lemma₂

  ds''-helper : P₂ → D
  ds''-helper (_ , _ , _ , _ , _ , ds'' , _) = ds''

  ds'' : D
  ds'' = ds''-helper Abp-lemma₂

  -- TODO
  postulate
    abp    : Abp (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'
    Fos₀'' : Fair os₀''
    Fos₁'' : Fair os₁''

  is'Bjs' : is' B js'
  is'Bjs' = not b , os₀'' , os₁'' , as'' , bs'' , cs'' , ds''
            , Sis' , not-Bool Bb , Fos₀'' , Fos₁'' , abp
