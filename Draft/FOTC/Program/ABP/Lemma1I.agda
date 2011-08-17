------------------------------------------------------------------------------
-- ABP lemma 1
------------------------------------------------------------------------------

-- From the paper: The first lemma states that given a start state Abp
-- (of the alternating bit protocol) we will arrive at a state Abp',
-- where the message has been received by the receiver, but where the
-- acknowledgement has not yet been received by the sender.

module Draft.FOTC.Program.ABP.Lemma1I where

open import FOTC.Base

open import Common.Function

open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.List

open import FOTC.Relation.Binary.EqReasoning

open import Draft.FOTC.Program.ABP.ABP
open import Draft.FOTC.Program.ABP.Fair
open import Draft.FOTC.Program.ABP.Fair.PropertiesI
open import Draft.FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

lemma₁-helper : ∀ {b i' is' os₀ os₁ as bs cs ds js} →
                Bit b →
                Fair os₁ →
                Abp b (i' ∷ is') os₀ os₁ as bs cs ds js →
                ∀ {ol₀} → O*L ol₀ →
                ∀ {os₀'-aux} → Fair os₀'-aux → os₀ ≡ ol₀ ++ os₀'-aux →
                ∃ λ os₀' → ∃ λ os₁' →
                ∃ λ as' → ∃ λ bs' → ∃ λ cs' → ∃ λ ds' → ∃ λ js' →
                Fair os₀'
                ∧ Fair os₁'
                ∧ Abp' b i' is' os₀' os₁' as' bs' cs' ds' js'
                ∧ js ≡ i' ∷ js'
lemma₁-helper {b} {i'} {is'} {os₀} {os₁} {as} {bs} {cs} {ds} {js}
              Bb Fos₁ (asAbp , bsAbp , csAbp , dsAbs , jsAbp)
              nilO*L {os₀'-aux = os₀'} Fos₀' os₀-eq =
                os₀' , os₁' , as' , bs' , cs' , ds' , js'
                , Fos₀' , Fos₁
                , (ds'-eq , refl , refl , refl , refl)
                , js-eq
  where
  os₀-eq-helper : os₀ ≡ L ∷ os₀'
  os₀-eq-helper =
    begin
      os₀              ≡⟨ os₀-eq ⟩
      (L ∷ []) ++ os₀' ≡⟨ ++-∷ L [] os₀' ⟩
      L ∷ ([] ++ os₀') ≡⟨ cong (_∷_ L) (++-[] os₀') ⟩
      L ∷ os₀'
    ∎

  as' : D
  as' = await b i' is' ds

  as-eq : as ≡ < i' , b > ∷ as'
  as-eq = trans asAbp (abpsend-eq b i' is' ds)

  bs' : D
  bs' = corrupt · os₀' · as'

  bs-eq : bs ≡ ok < i' , b > ∷ bs'
  bs-eq =
    begin
      bs
        ≡⟨ bsAbp ⟩
      corrupt · os₀ · as
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · os₀ · as ≡ corrupt · t₁ · t₂ )
                  os₀-eq-helper
                  as-eq
                  refl
        ⟩
      corrupt · (L ∷ os₀') · (< i' , b > ∷ as')
        ≡⟨ corrupt-L os₀' < i' , b > as' ⟩
      ok < i' , b > ∷ corrupt · os₀' · as'
        ≡⟨ refl ⟩
      ok < i' , b > ∷ bs'
    ∎

  cs' : D
  cs' = abpack · (not b) · bs'

  cs-eq : cs ≡ b ∷ cs'
  cs-eq =
    begin
      cs ≡⟨ csAbp ⟩
      abpack · b · bs
        ≡⟨ subst (λ t → abpack · b · bs ≡ abpack · b · t )
                 bs-eq
                 refl
        ⟩
      abpack · b · (ok < i' , b > ∷ bs')
        ≡⟨ abpack-ok≡ b b i' bs' refl ⟩
      b ∷ abpack · (not b) · bs'
        ≡⟨ refl ⟩
      b ∷ cs'
    ∎

  js' : D
  js' = abpout · (not b) · bs'

  js-eq : js ≡ i' ∷ js'
  js-eq =
    begin
      js
        ≡⟨ jsAbp ⟩
      abpout · b · bs
        ≡⟨ subst (λ t → abpout · b · bs ≡ abpout · b · t)
                 bs-eq
                 refl
        ⟩
      abpout · b · (ok < i' , b > ∷ bs') ≡⟨ abpout-ok≡ b b i' bs' refl ⟩
      i' ∷ abpout · (not b) · bs'        ≡⟨ refl ⟩
      i' ∷ js'
    ∎

  ds' : D
  ds' = ds

  os₁' : D
  os₁' = os₁

  ds'-eq =
    begin
      ds'
        ≡⟨ dsAbs ⟩
      corrupt · os₁ · cs
        ≡⟨ subst (λ t → corrupt · os₁ · cs ≡ corrupt · os₁ · t)
                 cs-eq
                 refl
        ⟩
      corrupt · os₁ · (b ∷ cs')
        ≡⟨ refl ⟩
      corrupt · os₁ · (b ∷ abpack · (not b) ·
              (corrupt · os₀' · (await b i' is' ds)))
    ∎

lemma₁-helper {b} {i'} {is'} {os₀} {os₁} {as} {bs} {cs} {ds} {js}
              Bb Fos₁ (asAbp , bsAbp , csAbp , dsAbs , jsAbp)
              (consO*L ol₀⁵ OLol₀⁵)
              {os₀'-aux = os₀'} Fos₀' os₀-eq =
                lemma₁-helper Bb (tail-Fair Fos₁) AbpIH OLol₀⁵ Fos₀' refl
  where
  os₀⁵ : D
  os₀⁵ = ol₀⁵ ++ os₀'

  os₁⁵ : D
  os₁⁵ = tail os₁

  os₀-eq-helper : os₀ ≡ O ∷ os₀⁵
  os₀-eq-helper =
    begin
      os₀                ≡⟨ os₀-eq ⟩
      (O ∷ ol₀⁵) ++ os₀' ≡⟨ ++-∷ O ol₀⁵ os₀' ⟩
      O ∷ ol₀⁵ ++ os₀'   ≡⟨ refl ⟩
      O ∷ os₀⁵
    ∎

  as⁵ : D
  as⁵ = await b i' is' ds

  as-eq : as ≡ < i' , b > ∷ as⁵
  as-eq = trans asAbp (abpsend-eq b i' is' ds)

  bs⁵ : D
  bs⁵ = corrupt · os₀⁵ · as⁵

  bs-eq : bs ≡ error ∷ bs⁵
  bs-eq =
    begin
      bs
        ≡⟨ bsAbp ⟩
      corrupt · os₀ · as
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · os₀ · as ≡ corrupt · t₁ · t₂)
                  os₀-eq-helper
                  as-eq
                  refl
        ⟩
      corrupt · (O ∷ os₀⁵) · (< i' , b > ∷ as⁵)
        ≡⟨ corrupt-O os₀⁵ < i' , b > as⁵ ⟩
      error ∷ corrupt · os₀⁵ · as⁵
        ≡⟨ refl ⟩
      error ∷ bs⁵
    ∎

  cs⁵ : D
  cs⁵ = abpack · b · bs⁵

  cs-eq : cs ≡ not b ∷ cs⁵
  cs-eq =
    begin
      cs
        ≡⟨ csAbp ⟩
      abpack · b · bs
        ≡⟨ subst (λ t → abpack · b · bs ≡ abpack · b · t)
                 bs-eq
                 refl
        ⟩
      abpack · b · (error ∷ bs⁵) ≡⟨ abpack-error b bs⁵ ⟩
      not b ∷ abpack · b · bs⁵   ≡⟨ refl ⟩
      not b ∷ cs⁵
    ∎

  ds⁵ : D
  ds⁵ = corrupt · os₁⁵ · cs⁵

  ds-eq-helper₁ : os₁ ≡ L ∷ tail os₁ → ds ≡ ok (not b) ∷ ds⁵
  ds-eq-helper₁ h =
    begin
      ds
        ≡⟨ dsAbs ⟩
      corrupt · os₁ · cs
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · os₁ · cs ≡ corrupt · t₁ · t₂)
                  h
                  cs-eq
                  refl
        ⟩
      corrupt · (L ∷ os₁⁵) · ((not b) ∷ cs⁵)
        ≡⟨ corrupt-L os₁⁵ (not b) cs⁵ ⟩
      ok (not b) ∷ corrupt · os₁⁵ · cs⁵
        ≡⟨ refl ⟩
      ok (not b) ∷ ds⁵
    ∎

  ds-eq-helper₂ : os₁ ≡ O ∷ tail os₁ → ds ≡ error ∷ ds⁵
  ds-eq-helper₂ h =
    begin
      ds
        ≡⟨ dsAbs ⟩
      corrupt · os₁ · cs
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · os₁ · cs ≡ corrupt · t₁ · t₂)
                  h
                  cs-eq
                  refl
        ⟩
      corrupt · (O ∷ os₁⁵) · ((not b) ∷ cs⁵)
        ≡⟨ corrupt-O os₁⁵ (not b) cs⁵ ⟩
      error ∷ corrupt · os₁⁵ · cs⁵
        ≡⟨ refl ⟩
      error ∷ ds⁵
    ∎

  ds-eq : ds ≡ ok (not b) ∷ ds⁵ ∨ ds ≡ error ∷ ds⁵
  ds-eq = [ (λ h → inj₁ (ds-eq-helper₁ h))
          , (λ h → inj₂ (ds-eq-helper₂ h))
          ] (head-tail-Fair Fos₁)

  as⁵-eq-helper₁ : ds ≡ ok (not b) ∷ ds⁵ → as⁵ ≡ abpsend · b · (i' ∷ is') · ds⁵
  as⁵-eq-helper₁ h =
    begin
      await b i' is' ds
        ≡⟨ cong (await b i' is') h ⟩
      await b i' is' (ok (not b) ∷ ds⁵)
        ≡⟨ await-ok≠ b (not b) i' is' ds⁵ (x≠not-x Bb) ⟩
      < i' , b > ∷ await b i' is' ds⁵
        ≡⟨ sym (abpsend-eq b i' is' ds⁵) ⟩
      abpsend · b · (i' ∷ is') · ds⁵
    ∎

  as⁵-eq-helper₂ : ds ≡ error ∷ ds⁵ → as⁵ ≡ abpsend · b · (i' ∷ is') · ds⁵
  as⁵-eq-helper₂ h =
    begin
      await b i' is' ds
        ≡⟨ cong (await b i' is') h ⟩
      await b i' is' (error ∷ ds⁵)
        ≡⟨ await-error b i' is' ds⁵ ⟩
      < i' , b > ∷ await b i' is' ds⁵
        ≡⟨ sym (abpsend-eq b i' is' ds⁵) ⟩
      abpsend · b · (i' ∷ is') · ds⁵
    ∎

  as⁵-eq : as⁵ ≡ abpsend · b · (i' ∷ is') · ds⁵
  as⁵-eq = [ as⁵-eq-helper₁ , as⁵-eq-helper₂ ] ds-eq

  js-eq : js ≡ abpout · b · bs⁵
  js-eq =
    begin
      js
        ≡⟨ jsAbp ⟩
      abpout · b · bs
        ≡⟨ subst (λ t → abpout · b · bs ≡ abpout · b · t)
                 bs-eq
                 refl
        ⟩
      abpout · b · (error ∷ bs⁵)
        ≡⟨ abpout-error b bs⁵ ⟩
      abpout · b · bs⁵
    ∎

  AbpIH : Abp b (i' ∷ is') os₀⁵ os₁⁵ as⁵ bs⁵ cs⁵ ds⁵ js
  AbpIH = as⁵-eq , refl , refl , refl , js-eq

-- From the paper: From the assumption that os₀ ∈ Fair, and hence by
-- unfolding Fair we conclude that there are ol₀ : O*L and os₀' :
-- Fair, such that
--
-- os₀ = ol₀ ++ os₀'.
--
-- We proceed by induction on ol₀ : O*L using lemma₁-helper.
lemma₁ : ∀ {b i' is' os₀ os₁ as bs cs ds js} →
         Bit b →
         Fair os₀ →
         Fair os₁ →
         Abp b (i' ∷ is') os₀ os₁ as bs cs ds js →
         ∃ λ os₀' → ∃ λ os₁' →
         ∃ λ as' → ∃ λ bs' → ∃ λ cs' → ∃ λ ds' → ∃ λ js' →
         Fair os₀'
         ∧ Fair os₁'
         ∧ Abp' b i' is' os₀' os₁' as' bs' cs' ds' js'
         ∧ js ≡ i' ∷ js'
lemma₁ {os₀ = os₀} Bb Fos₀ Fos₁ h = lemma₁-helper Bb Fos₁ h OLol₀ Fos₀' os₀-eq
  where
  unfold-os₀ : ∃ λ ol₀ → ∃ λ os₀' → O*L ol₀ ∧ Fair os₀' ∧ os₀ ≡ ol₀ ++ os₀'
  unfold-os₀ = Fair-gfp₁ Fos₀

  ol₀ : D
  ol₀ = ∃-proj₁ unfold-os₀

  os₀' : D
  os₀' = ∃-proj₁ (∃-proj₂ unfold-os₀)

  OLol₀ : O*L ol₀
  OLol₀ = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold-os₀))

  Fos₀' : Fair os₀'
  Fos₀' = ∧-proj₁ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-os₀)))

  os₀-eq : os₀ ≡ ol₀ ++ os₀'
  os₀-eq = ∧-proj₂ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-os₀)))
