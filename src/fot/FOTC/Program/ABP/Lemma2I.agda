------------------------------------------------------------------------------
-- ABP lemma 2
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From Dybjer and Sander's paper: The second lemma states that given
-- a state of the latter kind (see lemma 1) we will arrive at a new
-- start state, which is identical to the old start state except that
-- the bit has alternated and the first item in the input stream has
-- been removed.

module FOTC.Program.ABP.Lemma2I where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.List.PropertiesI
open import FOTC.Base.Loop
open import FOTC.Base.PropertiesI
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.PropertiesI
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Helper function for the ABP lemma 2

module Helper where

  helper : ∀ {b i' is' os₀' os₁' as' bs' cs' ds' js'} →
           Bit b →
           Fair os₀' →
           ABP' b i' is' os₀' os₁' as' bs' cs' ds' js' →
           ∃[ ft₁ ] ∃[ os₁'' ] F*T ft₁ ∧ Fair os₁'' ∧ os₁' ≡ ft₁ ++ os₁'' →
           ∃[ os₀'' ] ∃[ os₁'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
           Fair os₀''
           ∧ Fair os₁''
           ∧ ABP (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'
  helper {b} {i'} {is'} {os₀'} {os₁'} {as'} {bs'} {cs'} {ds'} {js'}
         Bb Fos₀' (ds'ABP' , as'ABP , bs'ABP' , cs'ABP' , js'ABP')
         (.(T ∷ []) , os₁'' , f*tnil , Fos₁'' , os₁'-eq) =
         os₀' , os₁'' , as'' , bs'' , cs'' , ds''
         , Fos₀' , Fos₁''
         , as''-eq , bs''-eq ,  cs''-eq , refl , js'-eq

    where
    os'₁-eq-helper : os₁' ≡ T ∷ os₁''
    os'₁-eq-helper =
      os₁'                 ≡⟨ os₁'-eq ⟩
      (true ∷ []) ++ os₁'' ≡⟨ ++-∷ true [] os₁'' ⟩
      true ∷ [] ++ os₁''   ≡⟨ ∷-rightCong (++-leftIdentity os₁'') ⟩
      true ∷ os₁''         ∎

    ds'' : D
    ds'' = corrupt · os₁'' · cs'

    ds'-eq : ds' ≡ ok b ∷ ds''
    ds'-eq =
      ds'
        ≡⟨ ds'ABP' ⟩
      corrupt · os₁' · (b ∷ cs')
        ≡⟨ ·-leftCong (·-rightCong os'₁-eq-helper) ⟩
      corrupt · (T ∷ os₁'') · (b ∷ cs')
        ≡⟨ corrupt-T os₁'' b cs' ⟩
      ok b ∷ corrupt · os₁'' · cs'
        ≡⟨ refl ⟩
      ok b ∷ ds'' ∎

    as'' : D
    as'' = as'

    as''-eq : as'' ≡ send · not b · is' · ds''
    as''-eq =
      as''                         ≡⟨ as'ABP ⟩
      await b i' is' ds'           ≡⟨ cong (await b i' is') ds'-eq ⟩
      await b i' is' (ok b ∷ ds'') ≡⟨ await-ok≡ b b i' is' ds'' refl ⟩
      send · not b · is' · ds''    ∎

    bs'' : D
    bs'' = bs'

    bs''-eq : bs'' ≡ corrupt · os₀' · as'
    bs''-eq = bs'ABP'

    cs'' : D
    cs'' = cs'

    cs''-eq : cs'' ≡ ack · not b · bs'
    cs''-eq = cs'ABP'

    js'-eq : js' ≡ out · not b · bs''
    js'-eq = js'ABP'

  helper {b} {i'} {is'} {os₀'} {os₁'} {as'} {bs'} {cs'} {ds'} {js'}
         Bb Fos₀' (ds'ABP' , as'ABP , bs'ABP' , cs'ABP' , js'ABP')
         (.(F ∷ ft₁) , os₁'' , f*tcons {ft₁} FTft₁ , Fos₁'' , os₁'-eq)
         = helper Bb (tail-Fair Fos₀') ABP'IH (ft₁ , os₁'' , FTft₁ , Fos₁'' , refl)

    where
    os₀⁵ : D
    os₀⁵ = tail₁ os₀'

    os₁⁵ : D
    os₁⁵ = ft₁ ++ os₁''

    os₁'-eq-helper : os₁' ≡ F ∷ os₁⁵
    os₁'-eq-helper = os₁'               ≡⟨ os₁'-eq ⟩
                     (F ∷ ft₁) ++ os₁'' ≡⟨ ++-∷ _ _ _ ⟩
                     F ∷ ft₁ ++ os₁''   ≡⟨ refl ⟩
                     F ∷ os₁⁵           ∎

    ds⁵ : D
    ds⁵ = corrupt · os₁⁵ · cs'

    ds'-eq : ds' ≡ error ∷ ds⁵
    ds'-eq =
      ds'
        ≡⟨ ds'ABP' ⟩
      corrupt · os₁' · (b ∷ cs')
        ≡⟨ ·-leftCong (·-rightCong os₁'-eq-helper) ⟩
      corrupt · (F ∷ os₁⁵) · (b ∷ cs')
        ≡⟨ corrupt-F _ _ _ ⟩
      error ∷ corrupt · os₁⁵ · cs'
        ≡⟨ refl ⟩
      error ∷ ds⁵ ∎

    as⁵ : D
    as⁵ = await b i' is' ds⁵

    as'-eq : as' ≡ < i' , b > ∷ as⁵
    as'-eq = as'                             ≡⟨ as'ABP ⟩
             await b i' is' ds'              ≡⟨ cong (await b i' is') ds'-eq ⟩
             await b i' is' (error ∷ ds⁵)    ≡⟨ await-error _ _ _ _ ⟩
             < i' , b > ∷ await b i' is' ds⁵ ≡⟨ refl ⟩
             < i' , b > ∷ as⁵                ∎

    bs⁵ : D
    bs⁵ = corrupt · os₀⁵ · as⁵

    bs'-eq-helper₁ : os₀' ≡ T ∷ tail₁ os₀' → bs' ≡ ok < i' , b > ∷ bs⁵
    bs'-eq-helper₁ h =
      bs'
        ≡⟨ bs'ABP' ⟩
      corrupt · os₀' · as'
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · os₀' · as' ≡ corrupt · t₁ · t₂)
                  h
                  as'-eq
                  refl
        ⟩
      corrupt · (T ∷ tail₁ os₀') · (< i' , b > ∷ as⁵)
        ≡⟨ corrupt-T _ _ _ ⟩
      ok < i' , b > ∷ corrupt · (tail₁ os₀') · as⁵
        ≡⟨ refl ⟩
      ok < i' , b > ∷ bs⁵ ∎

    bs'-eq-helper₂ : os₀' ≡ F ∷ tail₁ os₀' → bs' ≡ error ∷ bs⁵
    bs'-eq-helper₂ h =
      bs'
        ≡⟨ bs'ABP' ⟩
      corrupt · os₀' · as'
        ≡⟨ subst₂ (λ t₁ t₂ → corrupt · os₀' · as' ≡ corrupt · t₁ · t₂)
                  h
                  as'-eq
                  refl
        ⟩
      corrupt · (F ∷ tail₁ os₀') · (< i' , b > ∷ as⁵)
        ≡⟨ corrupt-F _ _ _ ⟩
      error ∷ corrupt · (tail₁ os₀') · as⁵
        ≡⟨ refl ⟩
      error ∷ bs⁵ ∎

    bs'-eq : bs' ≡ ok < i' , b > ∷ bs⁵ ∨ bs' ≡ error ∷ bs⁵
    bs'-eq = case (λ h → inj₁ (bs'-eq-helper₁ h))
                  (λ h → inj₂ (bs'-eq-helper₂ h))
                  (head-tail-Fair Fos₀')

    cs⁵ : D
    cs⁵ = ack · not b · bs⁵

    cs'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs⁵ → cs' ≡ b ∷ cs⁵
    cs'-eq-helper₁ h =
      cs'
      ≡⟨ cs'ABP' ⟩
      ack · not b · bs'
        ≡⟨ ·-rightCong h ⟩
      ack · not b · (ok < i' , b > ∷ bs⁵)
        ≡⟨ ack-ok≢ _ _ _ _ (not-x≢x Bb) ⟩
      not (not b) ∷ ack · not b · bs⁵
        ≡⟨ ∷-leftCong (not-involutive Bb) ⟩
      b ∷ ack · not b · bs⁵
        ≡⟨ refl ⟩
      b ∷ cs⁵ ∎

    cs'-eq-helper₂ : bs' ≡ error ∷ bs⁵ → cs' ≡ b ∷ cs⁵
    cs'-eq-helper₂ h =
      cs'                             ≡⟨ cs'ABP' ⟩
      ack · not b · bs'               ≡⟨ ·-rightCong h ⟩
      ack · not b · (error ∷ bs⁵)     ≡⟨ ack-error _ _ ⟩
      not (not b) ∷ ack · not b · bs⁵ ≡⟨ ∷-leftCong (not-involutive Bb) ⟩
      b ∷ ack · not b · bs⁵           ≡⟨ refl ⟩
      b ∷ cs⁵                         ∎

    cs'-eq : cs' ≡ b ∷ cs⁵
    cs'-eq = case cs'-eq-helper₁ cs'-eq-helper₂ bs'-eq

    js'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs⁵ → js' ≡ out · not b · bs⁵
    js'-eq-helper₁ h  =
      js'
        ≡⟨ js'ABP' ⟩
      out · not b · bs'
        ≡⟨ ·-rightCong h ⟩
      out · not b · (ok < i' , b > ∷ bs⁵)
        ≡⟨ out-ok≢ (not b) b i' bs⁵ (not-x≢x Bb) ⟩
      out · not b · bs⁵ ∎

    js'-eq-helper₂ : bs' ≡ error ∷ bs⁵ → js' ≡ out · not b · bs⁵
    js'-eq-helper₂ h  =
      js'                         ≡⟨ js'ABP' ⟩
      out · not b · bs'           ≡⟨ ·-rightCong h ⟩
      out · not b · (error ∷ bs⁵) ≡⟨ out-error (not b) bs⁵ ⟩
      out · not b · bs⁵           ∎

    js'-eq : js' ≡ out · not b · bs⁵
    js'-eq = case js'-eq-helper₁ js'-eq-helper₂ bs'-eq

    ds⁵-eq : ds⁵ ≡ corrupt · os₁⁵ · (b ∷ cs⁵)
    ds⁵-eq = ·-rightCong cs'-eq

    ABP'IH : ABP' b i' is' os₀⁵ os₁⁵ as⁵ bs⁵ cs⁵ ds⁵ js'
    ABP'IH = ds⁵-eq , refl , refl , refl , js'-eq

------------------------------------------------------------------------------
-- From Dybjer and Sander's paper: From the assumption that os₁ ∈
-- Fair, and hence by unfolding Fair we conclude that there are ft₁ :
-- F*T and os₁'' : Fair, such that os₁' = ft₁ ++ os₁''.
--
-- We proceed by induction on ft₁ : F*T using helper.

open Helper
lemma₂ : ∀ {b i' is' os₀' os₁' as' bs' cs' ds' js'} →
         Bit b →
         Fair os₀' →
         Fair os₁' →
         ABP' b i' is' os₀' os₁' as' bs' cs' ds' js' →
         ∃[ os₀'' ] ∃[ os₁'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
         Fair os₀''
         ∧ Fair os₁''
         ∧ ABP (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'
lemma₂ Bb Fos₀' Fos₁' abp' = helper Bb Fos₀' abp' (Fair-unf Fos₁')
