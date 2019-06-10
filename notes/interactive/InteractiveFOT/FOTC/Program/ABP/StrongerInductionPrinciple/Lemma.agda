------------------------------------------------------------------------------
-- ABP auxiliary lemma
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Program.ABP.StrongerInductionPrinciple.Lemma where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.Properties
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Base.Loop
open import Interactive.FOTC.Base.List.Properties
open import Interactive.FOTC.Data.Bool
open import Interactive.FOTC.Data.Bool.Properties
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Data.List.Properties
open import Interactive.FOTC.Program.ABP.ABP
open import Interactive.FOTC.Program.ABP.Fair.Type
open import Interactive.FOTC.Program.ABP.Fair.Properties
open import Interactive.FOTC.Program.ABP.Properties
open import Interactive.FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Helper function for the auxiliary lemma

module Helper where

  helper : ∀ {b i' is' os₁ os₂ as bs cs ds js} →
           Bit b →
           Fair os₂ →
           S b (i' ∷ is') os₁ os₂ as bs cs ds js →
           ∀ ft₁ os₁' → F*T ft₁ → Fair os₁' → os₁ ≡ ft₁ ++ os₁' →
           ∃[ js' ] js ≡ i' ∷ js'
  helper {b} {i'} {is'} {os₁} {os₂} {as} {bs} {cs} {ds} {js} Bb Fos₂
         (asS , bsS , csS , dsS , jsS)
         .(T ∷ []) os₁' f*tnil Fos₁' os₁-eq = js' , js-eq
    where
    os₁-eq-helper : os₁ ≡ T ∷ os₁'
    os₁-eq-helper = os₁              ≡⟨ os₁-eq ⟩
                    (T ∷ []) ++ os₁' ≡⟨ ++-∷ T [] os₁' ⟩
                    T ∷ ([] ++ os₁') ≡⟨ ∷-rightCong (++-leftIdentity os₁') ⟩
                    T ∷ os₁'         ∎

    as' : D
    as' = await b i' is' ds

    as-eq : as ≡ < i' , b > ∷ as'
    as-eq = trans asS (send-eq b i' is' ds)

    bs' : D
    bs' = corrupt os₁' · as'

    bs-eq : bs ≡ ok < i' , b > ∷ bs'
    bs-eq =
     bs ≡⟨ bsS ⟩
      corrupt os₁ · as
        ≡⟨ ·-rightCong as-eq ⟩
      corrupt os₁ · (< i' , b > ∷ as')
        ≡⟨ ·-leftCong (corruptCong os₁-eq-helper) ⟩
      corrupt (T ∷ os₁') · (< i' , b > ∷ as')
        ≡⟨ corrupt-T os₁' < i' , b > as' ⟩
      ok < i' , b > ∷ corrupt os₁' · as'
        ≡⟨ refl ⟩
      ok < i' , b > ∷ bs' ∎

    cs' : D
    cs' = ack (not b) · bs'

    js' : D
    js' = out (not b) · bs'

    js-eq : js ≡ i' ∷ js'
    js-eq = js                            ≡⟨ jsS ⟩
            out b · bs                    ≡⟨ ·-rightCong bs-eq ⟩
            out b · (ok < i' , b > ∷ bs') ≡⟨ out-ok≡ b b i' bs' refl ⟩
            i' ∷ out (not b) · bs'        ≡⟨ refl ⟩
            i' ∷ js'                      ∎

    ds' : D
    ds' = ds

  helper {b} {i'} {is'} {os₁} {os₂} {as} {bs} {cs} {ds} {js}
         Bb Fos₂ (asS , bsS , csS , dsS , jsS)
         .(F ∷ ft₁^) os₁' (f*tcons {ft₁^} FTft₁^) Fos₁' os₁-eq =
         helper Bb (tail-Fair Fos₂) ihS ft₁^ os₁' FTft₁^ Fos₁' refl

    where
    os₁^ : D
    os₁^ = ft₁^ ++ os₁'

    os₂^ : D
    os₂^ = tail₁ os₂

    os₁-eq-helper : os₁ ≡ F ∷ os₁^
    os₁-eq-helper = os₁                ≡⟨ os₁-eq ⟩
                    (F ∷ ft₁^) ++ os₁' ≡⟨ ++-∷ F ft₁^ os₁' ⟩
                    F ∷ ft₁^ ++ os₁'   ≡⟨ refl ⟩
                    F ∷ os₁^           ∎

    as^ : D
    as^ = await b i' is' ds

    as-eq : as ≡ < i' , b > ∷ as^
    as-eq = trans asS (send-eq b i' is' ds)

    bs^ : D
    bs^ = corrupt os₁^ · as^

    bs-eq : bs ≡ error ∷ bs^
    bs-eq =
      bs
        ≡⟨ bsS ⟩
      corrupt os₁ · as
        ≡⟨ ·-rightCong as-eq ⟩
      corrupt os₁ · (< i' , b > ∷ as^)
        ≡⟨ ·-leftCong (corruptCong os₁-eq-helper) ⟩
      corrupt (F ∷ os₁^) · (< i' , b > ∷ as^)
        ≡⟨ corrupt-F os₁^ < i' , b > as^ ⟩
      error ∷ corrupt os₁^ · as^
        ≡⟨ refl ⟩
      error ∷ bs^ ∎

    cs^ : D
    cs^ = ack b · bs^

    cs-eq : cs ≡ not b ∷ cs^
    cs-eq = cs                    ≡⟨ csS ⟩
            ack b · bs            ≡⟨ ·-rightCong bs-eq ⟩
            ack b · (error ∷ bs^) ≡⟨ ack-error b bs^ ⟩
            not b ∷ ack b · bs^   ≡⟨ refl ⟩
            not b ∷ cs^           ∎

    ds^ : D
    ds^ = corrupt os₂^ · cs^

    ds-eq-helper₁ : os₂ ≡ T ∷ tail₁ os₂ → ds ≡ ok (not b) ∷ ds^
    ds-eq-helper₁ h =
      ds                                 ≡⟨ dsS ⟩
      corrupt os₂ · cs                   ≡⟨ ·-rightCong cs-eq ⟩
      corrupt os₂ · (not b ∷ cs^)        ≡⟨ ·-leftCong (corruptCong h) ⟩
      corrupt (T ∷ os₂^) · (not b ∷ cs^) ≡⟨ corrupt-T os₂^ (not b) cs^ ⟩
      ok (not b) ∷ corrupt os₂^ · cs^    ≡⟨ refl ⟩
      ok (not b) ∷ ds^                   ∎

    ds-eq-helper₂ : os₂ ≡ F ∷ tail₁ os₂ → ds ≡ error ∷ ds^
    ds-eq-helper₂ h =
      ds                                 ≡⟨ dsS ⟩
      corrupt os₂ · cs                   ≡⟨ ·-rightCong cs-eq ⟩
      corrupt os₂ · (not b ∷ cs^)        ≡⟨ ·-leftCong (corruptCong h) ⟩
      corrupt (F ∷ os₂^) · (not b ∷ cs^) ≡⟨ corrupt-F os₂^ (not b) cs^ ⟩
      error ∷ corrupt os₂^ · cs^         ≡⟨ refl ⟩
      error ∷ ds^                        ∎

    ds-eq : ds ≡ ok (not b) ∷ ds^ ∨ ds ≡ error ∷ ds^
    ds-eq = case (λ h → inj₁ (ds-eq-helper₁ h))
                 (λ h → inj₂ (ds-eq-helper₂ h))
                 (head-tail-Fair Fos₂)

    as^-eq-helper₁ : ds ≡ ok (not b) ∷ ds^ → as^ ≡ send b · (i' ∷ is') · ds^
    as^-eq-helper₁ h =
      await b i' is' ds
        ≡⟨ awaitCong₄ h ⟩
      await b i' is' (ok (not b) ∷ ds^)
        ≡⟨ await-ok≢ b (not b) i' is' ds^ (x≢not-x Bb) ⟩
      < i' , b > ∷ await b i' is' ds^
        ≡⟨ sym (send-eq b i' is' ds^) ⟩
      send b · (i' ∷ is') · ds^ ∎

    as^-eq-helper₂ : ds ≡ error ∷ ds^ → as^ ≡ send b · (i' ∷ is') · ds^
    as^-eq-helper₂ h =
      await b i' is' ds               ≡⟨ awaitCong₄ h ⟩
      await b i' is' (error ∷ ds^)    ≡⟨ await-error b i' is' ds^ ⟩
      < i' , b > ∷ await b i' is' ds^ ≡⟨ sym (send-eq b i' is' ds^) ⟩
      send b · (i' ∷ is') · ds^     ∎

    as^-eq : as^ ≡ send b · (i' ∷ is') · ds^
    as^-eq = case as^-eq-helper₁ as^-eq-helper₂ ds-eq

    js-eq : js ≡ out b · bs^
    js-eq = js                    ≡⟨ jsS ⟩
            out b · bs            ≡⟨ ·-rightCong bs-eq ⟩
            out b · (error ∷ bs^) ≡⟨ out-error b bs^ ⟩
            out b · bs^ ∎

    ihS : S b (i' ∷ is') os₁^ os₂^ as^ bs^ cs^ ds^ js
    ihS = as^-eq , refl , refl , refl , js-eq

------------------------------------------------------------------------------
-- From Dybjer and Sander's paper: From the assumption that os₁ ∈ Fair
-- and hence by unfolding Fair, we conclude that there are ft₁ :  F*T
-- and os₁' : Fair, such that os₁ = ft₁ ++ os₁'.
--
-- We proceed by induction on ft₁ : F*T using helper.

open Helper
lemma : ∀ {b i' is' os₁ os₂ as bs cs ds js} →
         Bit b →
         Fair os₁ →
         Fair os₂ →
         S b (i' ∷ is') os₁ os₂ as bs cs ds js →
         ∃[ js' ] js ≡ i' ∷ js'
lemma Bb Fos₁ Fos₂ s with Fair-out Fos₁
... | ft , os₁' , FTft , prf ,  Fos₁' = helper Bb Fos₂ s ft os₁' FTft Fos₁' prf
