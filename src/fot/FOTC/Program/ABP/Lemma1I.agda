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
open import FOTC.Program.ABP.PropertiesI
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Helper function for the ABP lemma 1

module Helper where

  helper : ∀ {b i' is' os₀ os₁ as bs cs ds js} →
           Bit b →
           Fair os₁ →
           ABP b (i' ∷ is') os₀ os₁ as bs cs ds js →
           ∀ ft₀ os₀' → F*T ft₀ → Fair os₀' → os₀ ≡ ft₀ ++ os₀' →
           ∃[ os₀' ] ∃[ os₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
           Fair os₀'
           ∧ Fair os₁'
           ∧ ABP' b i' is' os₀' os₁' as' bs' cs' ds' js'
           ∧ js ≡ i' ∷ js'
  -- 2012-02-29. The existential witnesses could be avoid not using
  -- the auxiliary prooos inside the where clause.
  helper {b} {i'} {is'} {os₀} {os₁} {as} {bs} {cs} {ds} {js} Bb Fos₁
         (asABP , bsABP , csABP , dsAbs , jsABP)
         .(T ∷ []) os₀' f*tnil Fos₀' os₀-eq =
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
         .(F ∷ ft₀^) os₀' (f*tcons {ft₀^} FTft₀^) Fos₀' os₀-eq
         = helper Bb (tail-Fair Fos₁) ABPIH ft₀^  os₀' FTft₀^ Fos₀' refl

    where
    os₀^ : D
    os₀^ = ft₀^ ++ os₀'

    os₁^ : D
    os₁^ = tail₁ os₁

    os₀-eq-helper : os₀ ≡ F ∷ os₀^
    os₀-eq-helper = os₀                ≡⟨ os₀-eq ⟩
                    (F ∷ ft₀^) ++ os₀' ≡⟨ ++-∷ F ft₀^ os₀' ⟩
                    F ∷ ft₀^ ++ os₀'   ≡⟨ refl ⟩
                    F ∷ os₀^           ∎

    as^ : D
    as^ = await b i' is' ds

    as-eq : as ≡ < i' , b > ∷ as^
    as-eq = trans asABP (send-eq b i' is' ds)

    bs^ : D
    bs^ = corrupt · os₀^ · as^

    bs-eq : bs ≡ error ∷ bs^
    bs-eq =
      bs
        ≡⟨ bsABP ⟩
      corrupt · os₀ · as
        ≡⟨ ·-rightCong as-eq ⟩
      corrupt · os₀ · (< i' , b > ∷ as^)
        ≡⟨ ·-leftCong (·-rightCong os₀-eq-helper) ⟩
      corrupt · (F ∷ os₀^) · (< i' , b > ∷ as^)
        ≡⟨ corrupt-F os₀^ < i' , b > as^ ⟩
      error ∷ corrupt · os₀^ · as^
        ≡⟨ refl ⟩
      error ∷ bs^ ∎

    cs^ : D
    cs^ = ack · b · bs^

    cs-eq : cs ≡ not b ∷ cs^
    cs-eq = cs                      ≡⟨ csABP ⟩
            ack · b · bs            ≡⟨ ·-rightCong bs-eq ⟩
            ack · b · (error ∷ bs^) ≡⟨ ack-error b bs^ ⟩
            not b ∷ ack · b · bs^   ≡⟨ refl ⟩
            not b ∷ cs^             ∎

    ds^ : D
    ds^ = corrupt · os₁^ · cs^

    ds-eq-helper₁ : os₁ ≡ T ∷ tail₁ os₁ → ds ≡ ok (not b) ∷ ds^
    ds-eq-helper₁ h =
      ds                                   ≡⟨ dsAbs ⟩
      corrupt · os₁ · cs                   ≡⟨ ·-rightCong cs-eq ⟩
      corrupt · os₁ · (not b ∷ cs^)        ≡⟨ ·-leftCong (·-rightCong h) ⟩
      corrupt · (T ∷ os₁^) · (not b ∷ cs^) ≡⟨ corrupt-T os₁^ (not b) cs^ ⟩
      ok (not b) ∷ corrupt · os₁^ · cs^    ≡⟨ refl ⟩
      ok (not b) ∷ ds^                     ∎

    ds-eq-helper₂ : os₁ ≡ F ∷ tail₁ os₁ → ds ≡ error ∷ ds^
    ds-eq-helper₂ h =
      ds                                   ≡⟨ dsAbs ⟩
      corrupt · os₁ · cs                   ≡⟨ ·-rightCong cs-eq ⟩
      corrupt · os₁ · (not b ∷ cs^)        ≡⟨ ·-leftCong (·-rightCong h) ⟩
      corrupt · (F ∷ os₁^) · (not b ∷ cs^) ≡⟨ corrupt-F os₁^ (not b) cs^ ⟩
      error ∷ corrupt · os₁^ · cs^         ≡⟨ refl ⟩
      error ∷ ds^                          ∎

    ds-eq : ds ≡ ok (not b) ∷ ds^ ∨ ds ≡ error ∷ ds^
    ds-eq = case (λ h → inj₁ (ds-eq-helper₁ h))
                 (λ h → inj₂ (ds-eq-helper₂ h))
                 (head-tail-Fair Fos₁)

    as^-eq-helper₁ : ds ≡ ok (not b) ∷ ds^ → as^ ≡ send · b · (i' ∷ is') · ds^
    as^-eq-helper₁ h =
      await b i' is' ds
        ≡⟨ awaitCong₄ h ⟩
      await b i' is' (ok (not b) ∷ ds^)
        ≡⟨ await-ok≢ b (not b) i' is' ds^ (x≢not-x Bb) ⟩
      < i' , b > ∷ await b i' is' ds^
        ≡⟨ sym (send-eq b i' is' ds^) ⟩
      send · b · (i' ∷ is') · ds^ ∎

    as^-eq-helper₂ : ds ≡ error ∷ ds^ → as^ ≡ send · b · (i' ∷ is') · ds^
    as^-eq-helper₂ h =
      await b i' is' ds               ≡⟨ awaitCong₄ h ⟩
      await b i' is' (error ∷ ds^)    ≡⟨ await-error b i' is' ds^ ⟩
      < i' , b > ∷ await b i' is' ds^ ≡⟨ sym (send-eq b i' is' ds^) ⟩
      send · b · (i' ∷ is') · ds^     ∎

    as^-eq : as^ ≡ send · b · (i' ∷ is') · ds^
    as^-eq = case as^-eq-helper₁ as^-eq-helper₂ ds-eq

    js-eq : js ≡ out · b · bs^
    js-eq = js                      ≡⟨ jsABP ⟩
            out · b · bs            ≡⟨ ·-rightCong bs-eq ⟩
            out · b · (error ∷ bs^) ≡⟨ out-error b bs^ ⟩
            out · b · bs^ ∎

    ABPIH : ABP b (i' ∷ is') os₀^ os₁^ as^ bs^ cs^ ds^ js
    ABPIH = as^-eq , refl , refl , refl , js-eq

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
lemma₁ Bb Fos₀ Fos₁ abp with Fair-unf Fos₀
... | ft , os₀' , FTft , h ,  Fos₀' = helper Bb Fos₁ abp ft os₀' FTft Fos₀' h
