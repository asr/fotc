------------------------------------------------------------------------------
-- ABP lemma 1
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From Dybjer and Sander's paper: The first lemma states that given a
-- start state Abp (of the alternating bit protocol) we will arrive at
-- a state Abp', where the message has been received by the receiver,
-- but where the acknowledgement has not yet been received by the
-- sender.

module FOTC.Program.ABP.Lemma1I where

open import Common.Function

open import FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.List
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.PropertiesI
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Helper function for the ABP lemma 1

module Helper where

  helper : ∀ {b i' is' fs₀ fs₁ as bs cs ds js} →
           Bit b →
           Fair fs₁ →
           Abp b (i' ∷ is') fs₀ fs₁ as bs cs ds js →
           ∃[ ft₀ ] ∃[ fs₀' ] F*T ft₀ ∧ Fair fs₀' ∧ fs₀ ≡ ft₀ ++ fs₀' →
           ∃[ fs₀' ] ∃[ fs₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
           Fair fs₀'
           ∧ Fair fs₁'
           ∧ Abp' b i' is' fs₀' fs₁' as' bs' cs' ds' js'
           ∧ js ≡ i' ∷ js'
  -- 2012-02-28. We required the existential witness on the pattern matching.
  helper {b} {i'} {is'} {fs₀} {fs₁} {as} {bs} {cs} {ds} {js} Bb Ffs₁
         (asAbp , bsAbp , csAbp , dsAbs , jsAbp)
         (∃-intro (∃-intro {fs₀'} (nilF*T , Ffs₀' , fs₀-eq))) =
         ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $ ∃-intro $
           (Ffs₀' , Ffs₁ , (ds'-eq , refl , refl , refl , refl) , js-eq)
    where
    fs₀-eq-helper : fs₀ ≡ T ∷ fs₀'
    fs₀-eq-helper =
      fs₀              ≡⟨ fs₀-eq ⟩
      (T ∷ []) ++ fs₀' ≡⟨ ++-∷ T [] fs₀' ⟩
      T ∷ ([] ++ fs₀') ≡⟨ cong (_∷_ T) (++-[] fs₀') ⟩
      T ∷ fs₀' ∎

    as' : D
    as' = await b i' is' ds

    as-eq : as ≡ < i' , b > ∷ as'
    as-eq = trans asAbp (abpsend-eq b i' is' ds)

    bs' : D
    bs' = corrupt · fs₀' · as'

    bs-eq : bs ≡ ok < i' , b > ∷ bs'
    bs-eq =
      bs
        ≡⟨ bsAbp ⟩
      corrupt · fs₀ · as
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · fs₀ · as ≡ corrupt · t₁ · t₂ )
                  fs₀-eq-helper
                  as-eq
                  refl
        ⟩
      corrupt · (T ∷ fs₀') · (< i' , b > ∷ as')
        ≡⟨ corrupt-T fs₀' < i' , b > as' ⟩
      ok < i' , b > ∷ corrupt · fs₀' · as'
        ≡⟨ refl ⟩
      ok < i' , b > ∷ bs' ∎

    cs' : D
    cs' = abpack · (not b) · bs'

    cs-eq : cs ≡ b ∷ cs'
    cs-eq =
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
      b ∷ cs' ∎

    js' : D
    js' = abpout · (not b) · bs'

    js-eq : js ≡ i' ∷ js'
    js-eq =
      js
        ≡⟨ jsAbp ⟩
      abpout · b · bs
        ≡⟨ subst (λ t → abpout · b · bs ≡ abpout · b · t)
                 bs-eq
                 refl
        ⟩
      abpout · b · (ok < i' , b > ∷ bs')
        ≡⟨ abpout-ok≡ b b i' bs' refl ⟩
      i' ∷ abpout · (not b) · bs'
        ≡⟨ refl ⟩
      i' ∷ js' ∎

    ds' : D
    ds' = ds

    fs₁' : D
    fs₁' = fs₁

    ds'-eq : ds' ≡ corrupt · fs₁ · (b ∷ abpack · (not b) ·
                   (corrupt · fs₀' · (await b i' is' ds)))
    ds'-eq =
      ds'
        ≡⟨ dsAbs ⟩
      corrupt · fs₁ · cs
        ≡⟨ subst (λ t → corrupt · fs₁ · cs ≡ corrupt · fs₁ · t)
                 cs-eq
                 refl
        ⟩
      corrupt · fs₁ · (b ∷ cs')
        ≡⟨ refl ⟩
      corrupt · fs₁ · (b ∷ abpack · (not b) ·
                (corrupt · fs₀' · (await b i' is' ds))) ∎

  -- 2012-02-28. We required the existential witness on the pattern matching.
  helper {b} {i'} {is'} {fs₀} {fs₁} {as} {bs} {cs} {ds} {js}
         Bb Ffs₁ (asAbp , bsAbp , csAbp , dsAbs , jsAbp)
         (∃-intro (∃-intro {fs₀'} (consF*T {ft₀⁵} FTft₀⁵ , Ffs₀' , fs₀-eq)))
         = helper Bb
                  (tail-Fair Ffs₁)
                  AbpIH
                  (∃-intro (∃-intro (FTft₀⁵ , Ffs₀' , refl)))
    where
    fs₀⁵ : D
    fs₀⁵ = ft₀⁵ ++ fs₀'

    fs₁⁵ : D
    fs₁⁵ = tail₁ fs₁

    fs₀-eq-helper : fs₀ ≡ F ∷ fs₀⁵
    fs₀-eq-helper =
      fs₀                ≡⟨ fs₀-eq ⟩
      (F ∷ ft₀⁵) ++ fs₀' ≡⟨ ++-∷ F ft₀⁵ fs₀' ⟩
      F ∷ ft₀⁵ ++ fs₀'   ≡⟨ refl ⟩
      F ∷ fs₀⁵ ∎

    as⁵ : D
    as⁵ = await b i' is' ds

    as-eq : as ≡ < i' , b > ∷ as⁵
    as-eq = trans asAbp (abpsend-eq b i' is' ds)

    bs⁵ : D
    bs⁵ = corrupt · fs₀⁵ · as⁵

    bs-eq : bs ≡ error ∷ bs⁵
    bs-eq =
      bs
        ≡⟨ bsAbp ⟩
      corrupt · fs₀ · as
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · fs₀ · as ≡ corrupt · t₁ · t₂)
                  fs₀-eq-helper
                  as-eq
                  refl
        ⟩
      corrupt · (F ∷ fs₀⁵) · (< i' , b > ∷ as⁵)
        ≡⟨ corrupt-F fs₀⁵ < i' , b > as⁵ ⟩
      error ∷ corrupt · fs₀⁵ · as⁵
        ≡⟨ refl ⟩
      error ∷ bs⁵ ∎

    cs⁵ : D
    cs⁵ = abpack · b · bs⁵

    cs-eq : cs ≡ not b ∷ cs⁵
    cs-eq =
      cs
        ≡⟨ csAbp ⟩
      abpack · b · bs
        ≡⟨ subst (λ t → abpack · b · bs ≡ abpack · b · t)
                 bs-eq
                 refl
        ⟩
      abpack · b · (error ∷ bs⁵)
        ≡⟨ abpack-error b bs⁵ ⟩
      not b ∷ abpack · b · bs⁵
        ≡⟨ refl ⟩
      not b ∷ cs⁵ ∎

    ds⁵ : D
    ds⁵ = corrupt · fs₁⁵ · cs⁵

    ds-eq-helper₁ : fs₁ ≡ T ∷ tail₁ fs₁ → ds ≡ ok (not b) ∷ ds⁵
    ds-eq-helper₁ h =
      ds
        ≡⟨ dsAbs ⟩
      corrupt · fs₁ · cs
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · fs₁ · cs ≡ corrupt · t₁ · t₂)
                  h
                  cs-eq
                  refl
        ⟩
      corrupt · (T ∷ fs₁⁵) · ((not b) ∷ cs⁵)
        ≡⟨ corrupt-T fs₁⁵ (not b) cs⁵ ⟩
      ok (not b) ∷ corrupt · fs₁⁵ · cs⁵
        ≡⟨ refl ⟩
      ok (not b) ∷ ds⁵ ∎

    ds-eq-helper₂ : fs₁ ≡ F ∷ tail₁ fs₁ → ds ≡ error ∷ ds⁵
    ds-eq-helper₂ h =
      ds
        ≡⟨ dsAbs ⟩
      corrupt · fs₁ · cs
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · fs₁ · cs ≡ corrupt · t₁ · t₂)
                  h
                  cs-eq
                  refl
        ⟩
      corrupt · (F ∷ fs₁⁵) · ((not b) ∷ cs⁵)
        ≡⟨ corrupt-F fs₁⁵ (not b) cs⁵ ⟩
      error ∷ corrupt · fs₁⁵ · cs⁵
        ≡⟨ refl ⟩
      error ∷ ds⁵ ∎

    ds-eq : ds ≡ ok (not b) ∷ ds⁵ ∨ ds ≡ error ∷ ds⁵
    ds-eq = [ (λ h → inj₁ (ds-eq-helper₁ h))
            , (λ h → inj₂ (ds-eq-helper₂ h))
            ] (head-tail-Fair Ffs₁)

    as⁵-eq-helper₁ : ds ≡ ok (not b) ∷ ds⁵ → as⁵ ≡ abpsend · b · (i' ∷ is') · ds⁵
    as⁵-eq-helper₁ h =
      await b i' is' ds
        ≡⟨ cong (await b i' is') h ⟩
      await b i' is' (ok (not b) ∷ ds⁵)
        ≡⟨ await-ok≠ b (not b) i' is' ds⁵ (x≠not-x Bb) ⟩
      < i' , b > ∷ await b i' is' ds⁵
        ≡⟨ sym (abpsend-eq b i' is' ds⁵) ⟩
      abpsend · b · (i' ∷ is') · ds⁵ ∎

    as⁵-eq-helper₂ : ds ≡ error ∷ ds⁵ → as⁵ ≡ abpsend · b · (i' ∷ is') · ds⁵
    as⁵-eq-helper₂ h =
      await b i' is' ds
        ≡⟨ cong (await b i' is') h ⟩
      await b i' is' (error ∷ ds⁵)
        ≡⟨ await-error b i' is' ds⁵ ⟩
      < i' , b > ∷ await b i' is' ds⁵
        ≡⟨ sym (abpsend-eq b i' is' ds⁵) ⟩
      abpsend · b · (i' ∷ is') · ds⁵ ∎

    as⁵-eq : as⁵ ≡ abpsend · b · (i' ∷ is') · ds⁵
    as⁵-eq = [ as⁵-eq-helper₁ , as⁵-eq-helper₂ ] ds-eq

    js-eq : js ≡ abpout · b · bs⁵
    js-eq =
      js
        ≡⟨ jsAbp ⟩
      abpout · b · bs
        ≡⟨ subst (λ t → abpout · b · bs ≡ abpout · b · t)
                 bs-eq
                 refl
        ⟩
      abpout · b · (error ∷ bs⁵)
        ≡⟨ abpout-error b bs⁵ ⟩
      abpout · b · bs⁵ ∎

    AbpIH : Abp b (i' ∷ is') fs₀⁵ fs₁⁵ as⁵ bs⁵ cs⁵ ds⁵ js
    AbpIH = as⁵-eq , refl , refl , refl , js-eq

------------------------------------------------------------------------------
-- From Dybjer and Sander's paper: From the assumption that fs₀ ∈
-- Fair, and hence by unfolding Fair we conclude that there are ft₀ :
-- F*T and fs₀' : Fair, such that fs₀ = ft₀ ++ fs₀'.
--
-- We proceed by induction on ft₀ : F*T using helper.

open Helper
lemma₁ : ∀ {b i' is' fs₀ fs₁ as bs cs ds js} →
         Bit b →
         Fair fs₀ →
         Fair fs₁ →
         Abp b (i' ∷ is') fs₀ fs₁ as bs cs ds js →
         ∃[ fs₀' ] ∃[ fs₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
         Fair fs₀'
         ∧ Fair fs₁'
         ∧ Abp' b i' is' fs₀' fs₁' as' bs' cs' ds' js'
         ∧ js ≡ i' ∷ js'
lemma₁ Bb Ffs₀ Ffs₁ abp = helper Bb Ffs₁ abp (Fair-gfp₁ Ffs₀)
