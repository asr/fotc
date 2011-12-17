------------------------------------------------------------------------------
-- Helper function for the ABP lemma 2
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Lemma2.HelperI where

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.List
open import FOTC.Relation.Binary.EqReasoning
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.PropertiesI
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

helper : ∀ {b i' is' os₀' os₁' as' bs' cs' ds' js'} →
         Bit b →
         Fair os₀' →
         Abp' b i' is' os₀' os₁' as' bs' cs' ds' js' →
         ∀ {ol₁ os₁''-aux} →
         O*L ol₁ → Fair (os₁''-aux) → os₁' ≡ ol₁ ++ os₁''-aux →
         ∃ λ os₀'' → ∃ λ os₁'' →
         ∃ λ as'' → ∃ λ bs'' → ∃ λ cs'' → ∃ λ ds'' →
         Fair os₀''
         ∧ Fair os₁''
         ∧ Abp (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'
helper {b} {i'} {is'} {os₀'} {os₁'} {as'} {bs'} {cs'} {ds'} {js'}
       Bb Fos₀' (ds'Abp' , as'Abp , bs'Abp' , cs'Abp' , js'Abp')
       {os₁''-aux = os₁''} nilO*L Fos₁'' os₁'-eq =
         os₀' , os₁'' , as'' , bs'' , cs'' , ds''
         , Fos₀' , Fos₁''
         , as''-eq , bs''-eq ,  cs''-eq , refl , js'-eq
  where
  os'₁-eq-helper : os₁' ≡ L ∷ os₁''
  os'₁-eq-helper =
    begin
      os₁'                 ≡⟨ os₁'-eq ⟩
      (true ∷ []) ++ os₁'' ≡⟨ ++-∷ true [] os₁'' ⟩
      true ∷ [] ++ os₁''   ≡⟨ cong (_∷_ true) (++-[] os₁'') ⟩
      true ∷ os₁''
    ∎

  ds'' : D
  ds'' = corrupt · os₁'' · cs'

  ds'-eq : ds' ≡ ok b ∷ ds''
  ds'-eq =
    begin
      ds'
        ≡⟨ ds'Abp' ⟩
      corrupt · os₁' · (b ∷ cs')
        ≡⟨ subst (λ t → corrupt · os₁' · (b ∷ cs') ≡ corrupt · t · (b ∷ cs'))
                 os'₁-eq-helper
                 refl
        ⟩
      corrupt · (L ∷ os₁'') · (b ∷ cs')
        ≡⟨ corrupt-L os₁'' b cs' ⟩
      ok b ∷ corrupt · os₁'' · cs'
        ≡⟨ refl ⟩
      ok b ∷ ds''
    ∎

  as'' : D
  as'' = as'

  as''-eq : as'' ≡ abpsend · (not b) · is' · ds''
  as''-eq =
    begin
      as''                         ≡⟨ as'Abp ⟩
      await b i' is' ds'           ≡⟨ cong (await b i' is') ds'-eq ⟩
      await b i' is' (ok b ∷ ds'') ≡⟨ await-ok≡ b b i' is' ds'' refl ⟩
      abpsend · (not b) · is' · ds''
    ∎

  bs'' : D
  bs'' = bs'

  bs''-eq : bs'' ≡ corrupt · os₀' · as'
  bs''-eq = bs'Abp'

  cs'' : D
  cs'' = cs'

  cs''-eq : cs'' ≡ abpack · (not b) · bs'
  cs''-eq = cs'Abp'

  js'-eq : js' ≡ abpout · (not b) · bs''
  js'-eq = js'Abp'

helper {b} {i'} {is'} {os₀'} {os₁'} {as'} {bs'} {cs'} {ds'} {js'}
       Bb Fos₀' (ds'Abp' , as'Abp , bs'Abp' , cs'Abp' , js'Abp')
       {os₁''-aux = os₁''} (consO*L ol₁ OLol₁)
       Fos₁'' os₁'-eq = helper Bb (tail-Fair Fos₀') Abp'IH OLol₁ Fos₁'' refl

  where
  os₀⁵ : D
  os₀⁵ = tail₁ os₀'

  os₁⁵ : D
  os₁⁵ = ol₁ ++ os₁''

  os₁'-eq-helper : os₁' ≡ O ∷ os₁⁵
  os₁'-eq-helper =
    begin
      os₁'               ≡⟨ os₁'-eq ⟩
      (O ∷ ol₁) ++ os₁'' ≡⟨ ++-∷ _ _ _ ⟩
      O ∷ ol₁ ++ os₁''   ≡⟨ refl ⟩
      O ∷ os₁⁵
    ∎

  ds⁵ : D
  ds⁵ = corrupt · os₁⁵ · cs'

  ds'-eq : ds' ≡ error ∷ ds⁵
  ds'-eq =
    begin
      ds'
        ≡⟨ ds'Abp' ⟩
      corrupt · os₁' · (b ∷ cs')
        ≡⟨ subst (λ t → corrupt · os₁' · (b ∷ cs') ≡ corrupt · t · (b ∷ cs'))
                 os₁'-eq-helper
                 refl
        ⟩
      corrupt · (O ∷ os₁⁵) · (b ∷ cs')
        ≡⟨ corrupt-O _ _ _ ⟩
      error ∷ corrupt · os₁⁵ · cs'
        ≡⟨ refl ⟩
      error ∷ ds⁵
    ∎

  as⁵ : D
  as⁵ = await b i' is' ds⁵

  as'-eq : as' ≡ < i' , b > ∷ as⁵
  as'-eq =
    begin
      as'
        ≡⟨ as'Abp ⟩
      await b i' is' ds'
        ≡⟨ cong (await b i' is') ds'-eq ⟩
      await b i' is' (error ∷ ds⁵)
        ≡⟨ await-error _ _ _ _ ⟩
      < i' , b > ∷ await b i' is' ds⁵
        ≡⟨ refl ⟩
      < i' , b > ∷ as⁵
    ∎

  bs⁵ : D
  bs⁵ = corrupt · os₀⁵ · as⁵

  bs'-eq-helper₁ : os₀' ≡ L ∷ tail₁ os₀' → bs' ≡ ok < i' , b > ∷ bs⁵
  bs'-eq-helper₁ h =
    begin
      bs'
        ≡⟨ bs'Abp' ⟩
      corrupt · os₀' · as'
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · os₀' · as' ≡ corrupt · t₁ · t₂)
                  h
                  as'-eq
                  refl
        ⟩
      corrupt · (L ∷ tail₁ os₀') · (< i' , b > ∷ as⁵)
        ≡⟨ corrupt-L _ _ _ ⟩
      ok < i' , b > ∷ corrupt · (tail₁ os₀') · as⁵
        ≡⟨ refl ⟩
      ok < i' , b > ∷ bs⁵
    ∎

  bs'-eq-helper₂ : os₀' ≡ O ∷ tail₁ os₀' → bs' ≡ error ∷ bs⁵
  bs'-eq-helper₂ h =
    begin
      bs'
        ≡⟨ bs'Abp' ⟩
      corrupt · os₀' · as'
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · os₀' · as' ≡ corrupt · t₁ · t₂)
                  h
                  as'-eq
                  refl
        ⟩
      corrupt · (O ∷ tail₁ os₀') · (< i' , b > ∷ as⁵)
        ≡⟨ corrupt-O _ _ _ ⟩
      error ∷ corrupt · (tail₁ os₀') · as⁵
        ≡⟨ refl ⟩
      error ∷ bs⁵
    ∎

  bs'-eq : bs' ≡ ok < i' , b > ∷ bs⁵ ∨ bs' ≡ error ∷ bs⁵
  bs'-eq = [ (λ h → inj₁ (bs'-eq-helper₁ h))
           , (λ h → inj₂ (bs'-eq-helper₂ h))
           ] (head-tail-Fair Fos₀')


  cs⁵ : D
  cs⁵ = abpack · (not b) · bs⁵

  cs'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs⁵ → cs' ≡ b ∷ cs⁵
  cs'-eq-helper₁ h =
    begin
      cs'
      ≡⟨ cs'Abp' ⟩
      abpack · (not b) · bs'
        ≡⟨ subst (λ t → abpack · (not b) · bs' ≡ abpack · (not b) · t)
                 h
                 refl
        ⟩
      abpack · (not b) · (ok < i' , b > ∷ bs⁵)
        ≡⟨ abpack-ok≠ _ _ _ _ (not-x≠x Bb) ⟩
      not (not b) ∷ abpack · (not b) · bs⁵
        ≡⟨ subst (λ t → not (not b) ∷ abpack · (not b) · bs⁵ ≡
                        t           ∷ abpack · (not b) · bs⁵)
                 (not² Bb)
                 refl
        ⟩
      b ∷ abpack · (not b) · bs⁵
        ≡⟨ refl ⟩
      b ∷ cs⁵
    ∎

  cs'-eq-helper₂ : bs' ≡ error ∷ bs⁵ → cs' ≡ b ∷ cs⁵
  cs'-eq-helper₂ h =
    begin
      cs'
        ≡⟨ cs'Abp' ⟩
      abpack · (not b) · bs'
        ≡⟨ subst (λ t → abpack · (not b) · bs' ≡ abpack · (not b) · t)
                 h
                 refl
        ⟩
      abpack · (not b) · (error ∷ bs⁵)
        ≡⟨ abpack-error _ _ ⟩
      not (not b) ∷ abpack · (not b) · bs⁵
        ≡⟨ subst (λ t → not (not b) ∷ abpack · (not b) · bs⁵ ≡
                        t           ∷ abpack · (not b) · bs⁵)
                 (not² Bb)
                 refl
        ⟩
      b ∷ abpack · (not b) · bs⁵
        ≡⟨ refl ⟩
      b ∷ cs⁵
    ∎

  cs'-eq : cs' ≡ b ∷ cs⁵
  cs'-eq = [ cs'-eq-helper₁ , cs'-eq-helper₂ ] bs'-eq

  js'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs⁵ → js' ≡ abpout · (not b) · bs⁵
  js'-eq-helper₁ h  =
    begin
      js'
        ≡⟨ js'Abp' ⟩
      abpout · (not b) · bs'
        ≡⟨ subst (λ t → abpout · (not b) · bs' ≡ abpout · (not b) · t)
                 h
                 refl
        ⟩
      abpout · (not b) · (ok < i' , b > ∷ bs⁵)
        ≡⟨ abpout-ok≠ (not b) b i' bs⁵ (not-x≠x Bb) ⟩
      abpout · (not b) · bs⁵
    ∎

  js'-eq-helper₂ : bs' ≡ error ∷ bs⁵ → js' ≡ abpout · (not b) · bs⁵
  js'-eq-helper₂ h  =
    begin
      js' ≡⟨ js'Abp' ⟩
      abpout · (not b) · bs'
        ≡⟨ subst (λ t → abpout · (not b) · bs' ≡ abpout · (not b) · t)
                 h
                 refl
        ⟩
      abpout · (not b) · (error ∷ bs⁵)
        ≡⟨ abpout-error (not b) bs⁵ ⟩
      abpout · (not b) · bs⁵
    ∎

  js'-eq : js' ≡ abpout · (not b) · bs⁵
  js'-eq = [ js'-eq-helper₁ , js'-eq-helper₂ ] bs'-eq

  ds⁵-eq : ds⁵ ≡ corrupt · os₁⁵ · (b ∷ cs⁵)
  ds⁵-eq = trans refl (subst (λ t → corrupt · os₁⁵ · cs' ≡ corrupt · os₁⁵ · t )
                             cs'-eq
                             refl)

  Abp'IH : Abp' b i' is' os₀⁵ os₁⁵ as⁵ bs⁵ cs⁵ ds⁵ js'
  Abp'IH = ds⁵-eq , refl , refl , refl , js'-eq
