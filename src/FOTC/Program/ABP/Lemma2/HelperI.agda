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

helper : ∀ {b i' is' fs₀' fs₁' as' bs' cs' ds' js'} →
         Bit b →
         Fair fs₀' →
         Abp' b i' is' fs₀' fs₁' as' bs' cs' ds' js' →
         ∀ {ft₁ fs₁''-aux} →
         F*T ft₁ → Fair (fs₁''-aux) → fs₁' ≡ ft₁ ++ fs₁''-aux →
         ∃[ fs₀'' ] ∃[ fs₁'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
         Fair fs₀''
         ∧ Fair fs₁''
         ∧ Abp (not b) is' fs₀'' fs₁'' as'' bs'' cs'' ds'' js'
helper {b} {i'} {is'} {fs₀'} {fs₁'} {as'} {bs'} {cs'} {ds'} {js'}
       Bb Ffs₀' (ds'Abp' , as'Abp , bs'Abp' , cs'Abp' , js'Abp')
       {fs₁''-aux = fs₁''} nilF*T Ffs₁'' fs₁'-eq =
         fs₀' , fs₁'' , as'' , bs'' , cs'' , ds''
         , Ffs₀' , Ffs₁''
         , as''-eq , bs''-eq ,  cs''-eq , refl , js'-eq
  where
  fs'₁-eq-helper : fs₁' ≡ T ∷ fs₁''
  fs'₁-eq-helper =
    begin
      fs₁'                 ≡⟨ fs₁'-eq ⟩
      (true ∷ []) ++ fs₁'' ≡⟨ ++-∷ true [] fs₁'' ⟩
      true ∷ [] ++ fs₁''   ≡⟨ cong (_∷_ true) (++-[] fs₁'') ⟩
      true ∷ fs₁''
    ∎

  ds'' : D
  ds'' = corrupt · fs₁'' · cs'

  ds'-eq : ds' ≡ ok b ∷ ds''
  ds'-eq =
    begin
      ds'
        ≡⟨ ds'Abp' ⟩
      corrupt · fs₁' · (b ∷ cs')
        ≡⟨ subst (λ t → corrupt · fs₁' · (b ∷ cs') ≡ corrupt · t · (b ∷ cs'))
                 fs'₁-eq-helper
                 refl
        ⟩
      corrupt · (T ∷ fs₁'') · (b ∷ cs')
        ≡⟨ corrupt-T fs₁'' b cs' ⟩
      ok b ∷ corrupt · fs₁'' · cs'
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

  bs''-eq : bs'' ≡ corrupt · fs₀' · as'
  bs''-eq = bs'Abp'

  cs'' : D
  cs'' = cs'

  cs''-eq : cs'' ≡ abpack · (not b) · bs'
  cs''-eq = cs'Abp'

  js'-eq : js' ≡ abpout · (not b) · bs''
  js'-eq = js'Abp'

helper {b} {i'} {is'} {fs₀'} {fs₁'} {as'} {bs'} {cs'} {ds'} {js'}
       Bb Ffs₀' (ds'Abp' , as'Abp , bs'Abp' , cs'Abp' , js'Abp')
       {fs₁''-aux = fs₁''} (consF*T {ft₁} FTft₁)
       Ffs₁'' fs₁'-eq = helper Bb (tail-Fair Ffs₀') Abp'IH FTft₁ Ffs₁'' refl

  where
  fs₀⁵ : D
  fs₀⁵ = tail₁ fs₀'

  fs₁⁵ : D
  fs₁⁵ = ft₁ ++ fs₁''

  fs₁'-eq-helper : fs₁' ≡ F ∷ fs₁⁵
  fs₁'-eq-helper =
    begin
      fs₁'               ≡⟨ fs₁'-eq ⟩
      (F ∷ ft₁) ++ fs₁'' ≡⟨ ++-∷ _ _ _ ⟩
      F ∷ ft₁ ++ fs₁''   ≡⟨ refl ⟩
      F ∷ fs₁⁵
    ∎

  ds⁵ : D
  ds⁵ = corrupt · fs₁⁵ · cs'

  ds'-eq : ds' ≡ error ∷ ds⁵
  ds'-eq =
    begin
      ds'
        ≡⟨ ds'Abp' ⟩
      corrupt · fs₁' · (b ∷ cs')
        ≡⟨ subst (λ t → corrupt · fs₁' · (b ∷ cs') ≡ corrupt · t · (b ∷ cs'))
                 fs₁'-eq-helper
                 refl
        ⟩
      corrupt · (F ∷ fs₁⁵) · (b ∷ cs')
        ≡⟨ corrupt-F _ _ _ ⟩
      error ∷ corrupt · fs₁⁵ · cs'
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
  bs⁵ = corrupt · fs₀⁵ · as⁵

  bs'-eq-helper₁ : fs₀' ≡ T ∷ tail₁ fs₀' → bs' ≡ ok < i' , b > ∷ bs⁵
  bs'-eq-helper₁ h =
    begin
      bs'
        ≡⟨ bs'Abp' ⟩
      corrupt · fs₀' · as'
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · fs₀' · as' ≡ corrupt · t₁ · t₂)
                  h
                  as'-eq
                  refl
        ⟩
      corrupt · (T ∷ tail₁ fs₀') · (< i' , b > ∷ as⁵)
        ≡⟨ corrupt-T _ _ _ ⟩
      ok < i' , b > ∷ corrupt · (tail₁ fs₀') · as⁵
        ≡⟨ refl ⟩
      ok < i' , b > ∷ bs⁵
    ∎

  bs'-eq-helper₂ : fs₀' ≡ F ∷ tail₁ fs₀' → bs' ≡ error ∷ bs⁵
  bs'-eq-helper₂ h =
    begin
      bs'
        ≡⟨ bs'Abp' ⟩
      corrupt · fs₀' · as'
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · fs₀' · as' ≡ corrupt · t₁ · t₂)
                  h
                  as'-eq
                  refl
        ⟩
      corrupt · (F ∷ tail₁ fs₀') · (< i' , b > ∷ as⁵)
        ≡⟨ corrupt-F _ _ _ ⟩
      error ∷ corrupt · (tail₁ fs₀') · as⁵
        ≡⟨ refl ⟩
      error ∷ bs⁵
    ∎

  bs'-eq : bs' ≡ ok < i' , b > ∷ bs⁵ ∨ bs' ≡ error ∷ bs⁵
  bs'-eq = [ (λ h → inj₁ (bs'-eq-helper₁ h))
           , (λ h → inj₂ (bs'-eq-helper₂ h))
           ] (head-tail-Fair Ffs₀')


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

  ds⁵-eq : ds⁵ ≡ corrupt · fs₁⁵ · (b ∷ cs⁵)
  ds⁵-eq = trans refl (subst (λ t → corrupt · fs₁⁵ · cs' ≡ corrupt · fs₁⁵ · t )
                             cs'-eq
                             refl)

  Abp'IH : Abp' b i' is' fs₀⁵ fs₁⁵ as⁵ bs⁵ cs⁵ ds⁵ js'
  Abp'IH = ds⁵-eq , refl , refl , refl , js'-eq
