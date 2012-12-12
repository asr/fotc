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

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Base.List
open import FOTC.Base.Loop
open import FOTC.Base.List.PropertiesI
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.PropertiesI
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Helper function for the ABP lemma 1

module Helper where

  helper : ∀ {b i' is' os₀ os₁ as bs cs ds js} →
           Bit b →
           Fair os₁ →
           ABP b (i' ∷ is') os₀ os₁ as bs cs ds js →
           ∃[ ft₀ ] ∃[ os₀' ] F*T ft₀ ∧ Fair os₀' ∧ os₀ ≡ ft₀ ++ os₀' →
           ∃[ os₀' ] ∃[ os₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
           Fair os₀'
           ∧ Fair os₁'
           ∧ ABP' b i' is' os₀' os₁' as' bs' cs' ds' js'
           ∧ js ≡ i' ∷ js'
  -- 2012-02-29. The existential witnesses could be avoid not using
  -- the auxiliary prooos inside the where clause.
  helper {b} {i'} {is'} {os₀} {os₁} {as} {bs} {cs} {ds} {js} Bb Fos₁
         (asABP , bsABP , csABP , dsAbs , jsABP)
         (.(T ∷ []) , os₀' , f*tnil , Fos₀' , os₀-eq) =
         os₀' , os₁' , as' , bs' , cs' , ds' , js'
         , Fos₀' , Fos₁
         , (ds'-eq , refl , refl , refl , refl)
         , js-eq

    where
    os₀-eq-helper : os₀ ≡ T ∷ os₀'
    os₀-eq-helper = os₀              ≡⟨ os₀-eq ⟩
                    (T ∷ []) ++ os₀' ≡⟨ ++-∷ T [] os₀' ⟩
                    T ∷ ([] ++ os₀') ≡⟨ ∷-rightCong (++-leftIdentity os₀') ⟩
                    T ∷ os₀'         ∎

    as' : D
    as' = await b i' is' ds

    as-eq : as ≡ < i' , b > ∷ as'
    as-eq = trans asABP (send-eq b i' is' ds)

    bs' : D
    bs' = corrupt · os₀' · as'

    bs-eq : bs ≡ ok < i' , b > ∷ bs'
    bs-eq =
     bs
        ≡⟨ bsABP ⟩
      corrupt · os₀ · as
        ≡⟨ ·-rightCong as-eq ⟩
      corrupt · os₀ · (< i' , b > ∷ as')
        ≡⟨ ·-leftCong (·-rightCong os₀-eq-helper) ⟩
          corrupt · (T ∷ os₀') · (< i' , b > ∷ as')
        ≡⟨ corrupt-T os₀' < i' , b > as' ⟩
      ok < i' , b > ∷ corrupt · os₀' · as'
        ≡⟨ refl ⟩
      ok < i' , b > ∷ bs' ∎

    cs' : D
    cs' = ack · not b · bs'

    cs-eq : cs ≡ b ∷ cs'
    cs-eq = cs                              ≡⟨ csABP ⟩
            ack · b · bs                    ≡⟨ ·-rightCong bs-eq ⟩
            ack · b · (ok < i' , b > ∷ bs') ≡⟨ ack-ok≡ b b i' bs' refl ⟩
            b ∷ ack · not b · bs'           ≡⟨ refl ⟩
            b ∷ cs'                         ∎

    js' : D
    js' = out · not b · bs'

    js-eq : js ≡ i' ∷ js'
    js-eq = js                              ≡⟨ jsABP ⟩
            out · b · bs                    ≡⟨ ·-rightCong bs-eq ⟩
            out · b · (ok < i' , b > ∷ bs') ≡⟨ out-ok≡ b b i' bs' refl ⟩
            i' ∷ out · not b · bs'          ≡⟨ refl ⟩
            i' ∷ js'                        ∎

    ds' : D
    ds' = ds

    os₁' : D
    os₁' = os₁

    ds'-eq : ds' ≡ corrupt · os₁ · (b ∷ ack · not b ·
                   (corrupt · os₀' · (await b i' is' ds)))
    ds'-eq =
      ds'
        ≡⟨ dsAbs ⟩
      corrupt · os₁ · cs
        ≡⟨ ·-rightCong cs-eq ⟩
      corrupt · os₁ · (b ∷ cs')
        ≡⟨ refl ⟩
      corrupt · os₁ · (b ∷ ack · not b ·
                (corrupt · os₀' · (await b i' is' ds))) ∎

  helper {b} {i'} {is'} {os₀} {os₁} {as} {bs} {cs} {ds} {js}
         Bb Fos₁ (asABP , bsABP , csABP , dsAbs , jsABP)
         (.(F ∷ ft₀⁵) , os₀' , f*tcons {ft₀⁵} FTft₀⁵ , Fos₀' , os₀-eq)
         = helper Bb (tail-Fair Fos₁) ABPIH (ft₀⁵ , os₀' , FTft₀⁵ , Fos₀' , refl)

    where
    os₀⁵ : D
    os₀⁵ = ft₀⁵ ++ os₀'

    os₁⁵ : D
    os₁⁵ = tail₁ os₁

    os₀-eq-helper : os₀ ≡ F ∷ os₀⁵
    os₀-eq-helper = os₀                ≡⟨ os₀-eq ⟩
                    (F ∷ ft₀⁵) ++ os₀' ≡⟨ ++-∷ F ft₀⁵ os₀' ⟩
                    F ∷ ft₀⁵ ++ os₀'   ≡⟨ refl ⟩
                    F ∷ os₀⁵           ∎

    as⁵ : D
    as⁵ = await b i' is' ds

    as-eq : as ≡ < i' , b > ∷ as⁵
    as-eq = trans asABP (send-eq b i' is' ds)

    bs⁵ : D
    bs⁵ = corrupt · os₀⁵ · as⁵

    bs-eq : bs ≡ error ∷ bs⁵
    bs-eq =
      bs
        ≡⟨ bsABP ⟩
      corrupt · os₀ · as
        ≡⟨ ·-rightCong as-eq ⟩
      corrupt · os₀ · (< i' , b > ∷ as⁵)
        ≡⟨ ·-leftCong (·-rightCong os₀-eq-helper) ⟩
      corrupt · (F ∷ os₀⁵) · (< i' , b > ∷ as⁵)
        ≡⟨ corrupt-F os₀⁵ < i' , b > as⁵ ⟩
      error ∷ corrupt · os₀⁵ · as⁵
        ≡⟨ refl ⟩
      error ∷ bs⁵ ∎

    cs⁵ : D
    cs⁵ = ack · b · bs⁵

    cs-eq : cs ≡ not b ∷ cs⁵
    cs-eq = cs                      ≡⟨ csABP ⟩
            ack · b · bs            ≡⟨ ·-rightCong bs-eq ⟩
            ack · b · (error ∷ bs⁵) ≡⟨ ack-error b bs⁵ ⟩
            not b ∷ ack · b · bs⁵   ≡⟨ refl ⟩
            not b ∷ cs⁵             ∎

    ds⁵ : D
    ds⁵ = corrupt · os₁⁵ · cs⁵

    ds-eq-helper₁ : os₁ ≡ T ∷ tail₁ os₁ → ds ≡ ok (not b) ∷ ds⁵
    ds-eq-helper₁ h =
      ds                                   ≡⟨ dsAbs ⟩
      corrupt · os₁ · cs                   ≡⟨ ·-rightCong cs-eq ⟩
      corrupt · os₁ · (not b ∷ cs⁵)        ≡⟨ ·-leftCong (·-rightCong h) ⟩
      corrupt · (T ∷ os₁⁵) · (not b ∷ cs⁵) ≡⟨ corrupt-T os₁⁵ (not b) cs⁵ ⟩
      ok (not b) ∷ corrupt · os₁⁵ · cs⁵    ≡⟨ refl ⟩
      ok (not b) ∷ ds⁵                     ∎

    ds-eq-helper₂ : os₁ ≡ F ∷ tail₁ os₁ → ds ≡ error ∷ ds⁵
    ds-eq-helper₂ h =
      ds                                   ≡⟨ dsAbs ⟩
      corrupt · os₁ · cs                   ≡⟨ ·-rightCong cs-eq ⟩
      corrupt · os₁ · (not b ∷ cs⁵)        ≡⟨ ·-leftCong (·-rightCong h) ⟩
      corrupt · (F ∷ os₁⁵) · (not b ∷ cs⁵) ≡⟨ corrupt-F os₁⁵ (not b) cs⁵ ⟩
      error ∷ corrupt · os₁⁵ · cs⁵         ≡⟨ refl ⟩
      error ∷ ds⁵                          ∎

    ds-eq : ds ≡ ok (not b) ∷ ds⁵ ∨ ds ≡ error ∷ ds⁵
    ds-eq = case (λ h → inj₁ (ds-eq-helper₁ h))
                 (λ h → inj₂ (ds-eq-helper₂ h))
                 (head-tail-Fair Fos₁)

    as⁵-eq-helper₁ : ds ≡ ok (not b) ∷ ds⁵ → as⁵ ≡ send · b · (i' ∷ is') · ds⁵
    as⁵-eq-helper₁ h =
      await b i' is' ds
        ≡⟨ cong (await b i' is') h ⟩
      await b i' is' (ok (not b) ∷ ds⁵)
        ≡⟨ await-ok≢ b (not b) i' is' ds⁵ (x≢not-x Bb) ⟩
      < i' , b > ∷ await b i' is' ds⁵
        ≡⟨ sym (send-eq b i' is' ds⁵) ⟩
      send · b · (i' ∷ is') · ds⁵ ∎

    as⁵-eq-helper₂ : ds ≡ error ∷ ds⁵ → as⁵ ≡ send · b · (i' ∷ is') · ds⁵
    as⁵-eq-helper₂ h =
      await b i' is' ds               ≡⟨ cong (await b i' is') h ⟩
      await b i' is' (error ∷ ds⁵)    ≡⟨ await-error b i' is' ds⁵ ⟩
      < i' , b > ∷ await b i' is' ds⁵ ≡⟨ sym (send-eq b i' is' ds⁵) ⟩
      send · b · (i' ∷ is') · ds⁵     ∎

    as⁵-eq : as⁵ ≡ send · b · (i' ∷ is') · ds⁵
    as⁵-eq = case as⁵-eq-helper₁ as⁵-eq-helper₂ ds-eq

    js-eq : js ≡ out · b · bs⁵
    js-eq = js                      ≡⟨ jsABP ⟩
            out · b · bs            ≡⟨ ·-rightCong bs-eq ⟩
            out · b · (error ∷ bs⁵) ≡⟨ out-error b bs⁵ ⟩
            out · b · bs⁵ ∎

    ABPIH : ABP b (i' ∷ is') os₀⁵ os₁⁵ as⁵ bs⁵ cs⁵ ds⁵ js
    ABPIH = as⁵-eq , refl , refl , refl , js-eq

------------------------------------------------------------------------------
-- From Dybjer and Sander's paper: From the assumption that os₀ ∈
-- Fair, and hence by unfolding Fair we conclude that there are ft₀ :
-- F*T and os₀' : Fair, such that os₀ = ft₀ ++ os₀'.
--
-- We proceed by induction on ft₀ : F*T using helper.

open Helper
lemma₁ : ∀ {b i' is' os₀ os₁ as bs cs ds js} →
         Bit b →
         Fair os₀ →
         Fair os₁ →
         ABP b (i' ∷ is') os₀ os₁ as bs cs ds js →
         ∃[ os₀' ] ∃[ os₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
         Fair os₀'
         ∧ Fair os₁'
         ∧ ABP' b i' is' os₀' os₁' as' bs' cs' ds' js'
         ∧ js ≡ i' ∷ js'
lemma₁ Bb Fos₀ Fos₁ abp = helper Bb Fos₁ abp (Fair-unf Fos₀)
