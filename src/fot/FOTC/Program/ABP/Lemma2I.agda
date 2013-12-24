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
open import FOTC.Program.ABP.Fair.Type
open import FOTC.Program.ABP.Fair.PropertiesI
open import FOTC.Program.ABP.PropertiesI
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Helper function for the ABP lemma 2

module Helper where

  helper : ∀ {b i' is' os₁' os₂' as' bs' cs' ds' js'} →
           Bit b →
           Fair os₁' →
           S' b i' is' os₁' os₂' as' bs' cs' ds' js' →
           ∀ ft₂ os₂'' → F*T ft₂ → Fair os₂'' → os₂' ≡ ft₂ ++ os₂'' →
           ∃[ os₁'' ] ∃[ os₂'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
             Fair os₁''
             ∧ Fair os₂''
             ∧ S (not b) is' os₁'' os₂'' as'' bs'' cs'' ds'' js'
  helper {b} {i'} {is'} {os₁'} {os₂'} {as'} {bs'} {cs'} {ds'} {js'}
         Bb Fos₁' (as'S' , bs'S' , cs'S' , ds'S' , js'S')
         .(T ∷ []) os₂'' f*tnil Fos₂'' os₂'-eq =
         os₁' , os₂'' , as'' , bs'' , cs'' , ds''
         , Fos₁' , Fos₂''
         , as''-eq , bs''-eq ,  cs''-eq , refl , js'-eq

    where
    os₂'-eq-helper : os₂' ≡ T ∷ os₂''
    os₂'-eq-helper =
      os₂'                 ≡⟨ os₂'-eq ⟩
      (true ∷ []) ++ os₂'' ≡⟨ ++-∷ true [] os₂'' ⟩
      true ∷ [] ++ os₂''   ≡⟨ ∷-rightCong (++-leftIdentity os₂'') ⟩
      true ∷ os₂''         ∎

    ds'' : D
    ds'' = corrupt os₂'' · cs'

    ds'-eq : ds' ≡ ok b ∷ ds''
    ds'-eq =
      ds' ≡⟨ ds'S' ⟩
      corrupt os₂' · (b ∷ cs')
        ≡⟨ ·-leftCong (corruptCong os₂'-eq-helper) ⟩
      corrupt (T ∷ os₂'') · (b ∷ cs')
        ≡⟨ corrupt-T os₂'' b cs' ⟩
      ok b ∷ corrupt os₂'' · cs'
        ≡⟨ refl ⟩
      ok b ∷ ds'' ∎

    as'' : D
    as'' = as'

    as''-eq : as'' ≡ send (not b) · is' · ds''
    as''-eq =
      as''                         ≡⟨ as'S' ⟩
      await b i' is' ds'           ≡⟨ awaitCong₄ ds'-eq ⟩
      await b i' is' (ok b ∷ ds'') ≡⟨ await-ok≡ b b i' is' ds'' refl ⟩
      send (not b) · is' · ds''    ∎

    bs'' : D
    bs'' = bs'

    bs''-eq : bs'' ≡ corrupt os₁' · as'
    bs''-eq = bs'S'

    cs'' : D
    cs'' = cs'

    cs''-eq : cs'' ≡ ack (not b) · bs'
    cs''-eq = cs'S'

    js'-eq : js' ≡ out (not b) · bs''
    js'-eq = js'S'

  helper {b} {i'} {is'} {os₁'} {os₂'} {as'} {bs'} {cs'} {ds'} {js'}
         Bb Fos₁' (as'S' , bs'S' , cs'S' , ds'S' , js'S')
         .(F ∷ ft₂) os₂'' (f*tcons {ft₂} FTft₂) Fos₂'' os₂'-eq =
         helper Bb (tail-Fair Fos₁') ihS' ft₂ os₂'' FTft₂ Fos₂'' refl

    where
    os₁^ : D
    os₁^ = tail₁ os₁'

    os₂^ : D
    os₂^ = ft₂ ++ os₂''

    os₂'-eq-helper : os₂' ≡ F ∷ os₂^
    os₂'-eq-helper = os₂'               ≡⟨ os₂'-eq ⟩
                     (F ∷ ft₂) ++ os₂'' ≡⟨ ++-∷ _ _ _ ⟩
                     F ∷ ft₂ ++ os₂''   ≡⟨ refl ⟩
                     F ∷ os₂^           ∎

    ds^ : D
    ds^ = corrupt os₂^ · cs'

    ds'-eq : ds' ≡ error ∷ ds^
    ds'-eq =
      ds'
        ≡⟨ ds'S' ⟩
      corrupt os₂' · (b ∷ cs')
        ≡⟨ ·-leftCong (corruptCong os₂'-eq-helper) ⟩
      corrupt (F ∷ os₂^) · (b ∷ cs')
        ≡⟨ corrupt-F _ _ _ ⟩
      error ∷ corrupt os₂^ · cs'
        ≡⟨ refl ⟩
      error ∷ ds^ ∎

    as^ : D
    as^ = await b i' is' ds^

    as'-eq : as' ≡ < i' , b > ∷ as^
    as'-eq = as'                             ≡⟨ as'S' ⟩
             await b i' is' ds'              ≡⟨ awaitCong₄ ds'-eq ⟩
             await b i' is' (error ∷ ds^)    ≡⟨ await-error _ _ _ _ ⟩
             < i' , b > ∷ await b i' is' ds^ ≡⟨ refl ⟩
             < i' , b > ∷ as^                ∎

    bs^ : D
    bs^ = corrupt os₁^ · as^

    bs'-eq-helper₁ : os₁' ≡ T ∷ tail₁ os₁' → bs' ≡ ok < i' , b > ∷ bs^
    bs'-eq-helper₁ h =
      bs'
        ≡⟨ bs'S' ⟩
      corrupt os₁' · as'
        ≡⟨ subst₂ (λ t t' → corrupt os₁' · as' ≡ corrupt t · t')
                  h
                  as'-eq
                  refl
        ⟩
      corrupt (T ∷ tail₁ os₁') · (< i' , b > ∷ as^)
        ≡⟨ corrupt-T _ _ _ ⟩
      ok < i' , b > ∷ corrupt (tail₁ os₁') · as^
        ≡⟨ refl ⟩
      ok < i' , b > ∷ bs^ ∎

    bs'-eq-helper₂ : os₁' ≡ F ∷ tail₁ os₁' → bs' ≡ error ∷ bs^
    bs'-eq-helper₂ h =
      bs'
        ≡⟨ bs'S' ⟩
      corrupt os₁' · as'
        ≡⟨ subst₂ (λ t t' → corrupt os₁' · as' ≡ corrupt t · t')
                  h
                  as'-eq
                  refl
        ⟩
      corrupt (F ∷ tail₁ os₁') · (< i' , b > ∷ as^)
        ≡⟨ corrupt-F _ _ _ ⟩
      error ∷ corrupt (tail₁ os₁') · as^
        ≡⟨ refl ⟩
      error ∷ bs^ ∎

    bs'-eq : bs' ≡ ok < i' , b > ∷ bs^ ∨ bs' ≡ error ∷ bs^
    bs'-eq = case (λ h → inj₁ (bs'-eq-helper₁ h))
                  (λ h → inj₂ (bs'-eq-helper₂ h))
                  (head-tail-Fair Fos₁')

    cs^ : D
    cs^ = ack (not b) · bs^

    cs'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs^ → cs' ≡ b ∷ cs^
    cs'-eq-helper₁ h =
      cs'
      ≡⟨ cs'S' ⟩
      ack (not b) · bs'
        ≡⟨ ·-rightCong h ⟩
      ack (not b) · (ok < i' , b > ∷ bs^)
        ≡⟨ ack-ok≢ _ _ _ _ (not-x≢x Bb) ⟩
      not (not b) ∷ ack (not b) · bs^
        ≡⟨ ∷-leftCong (not-involutive Bb) ⟩
      b ∷ ack (not b) · bs^
        ≡⟨ refl ⟩
      b ∷ cs^ ∎

    cs'-eq-helper₂ : bs' ≡ error ∷ bs^ → cs' ≡ b ∷ cs^
    cs'-eq-helper₂ h =
      cs'                             ≡⟨ cs'S' ⟩
      ack (not b) · bs'               ≡⟨ ·-rightCong h ⟩
      ack (not b) · (error ∷ bs^)     ≡⟨ ack-error _ _ ⟩
      not (not b) ∷ ack (not b) · bs^ ≡⟨ ∷-leftCong (not-involutive Bb) ⟩
      b ∷ ack (not b) · bs^           ≡⟨ refl ⟩
      b ∷ cs^                         ∎

    cs'-eq : cs' ≡ b ∷ cs^
    cs'-eq = case cs'-eq-helper₁ cs'-eq-helper₂ bs'-eq

    js'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs^ → js' ≡ out (not b) · bs^
    js'-eq-helper₁ h  =
      js'
        ≡⟨ js'S' ⟩
      out (not b) · bs'
        ≡⟨ ·-rightCong h ⟩
      out (not b) · (ok < i' , b > ∷ bs^)
        ≡⟨ out-ok≢ (not b) b i' bs^ (not-x≢x Bb) ⟩
      out (not b) · bs^ ∎

    js'-eq-helper₂ : bs' ≡ error ∷ bs^ → js' ≡ out (not b) · bs^
    js'-eq-helper₂ h  =
      js'                         ≡⟨ js'S' ⟩
      out (not b) · bs'           ≡⟨ ·-rightCong h ⟩
      out (not b) · (error ∷ bs^) ≡⟨ out-error (not b) bs^ ⟩
      out (not b) · bs^           ∎

    js'-eq : js' ≡ out (not b) · bs^
    js'-eq = case js'-eq-helper₁ js'-eq-helper₂ bs'-eq

    ds^-eq : ds^ ≡ corrupt os₂^ · (b ∷ cs^)
    ds^-eq = ·-rightCong cs'-eq

    ihS' : S' b i' is' os₁^ os₂^ as^ bs^ cs^ ds^ js'
    ihS' = refl , refl , refl , ds^-eq , js'-eq

------------------------------------------------------------------------------
-- From Dybjer and Sander's paper: From the assumption that
-- os₂' ∈ Fair and hence by unfolding Fair, we conclude that there are
-- ft₂ : F*T and os₂'' : Fair, such that os₂' = ft₂ ++ os₂''.
--
-- We proceed by induction on ft₂ : F*T using helper.

open Helper
lemma₂ : ∀ {b i' is' os₁' os₂' as' bs' cs' ds' js'} →
         Bit b →
         Fair os₁' →
         Fair os₂' →
         S' b i' is' os₁' os₂' as' bs' cs' ds' js' →
         ∃[ os₁'' ] ∃[ os₂'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
         Fair os₁''
         ∧ Fair os₂''
         ∧ S (not b) is' os₁'' os₂'' as'' bs'' cs'' ds'' js'
lemma₂ Bb Fos₁' Fos₂' s' with Fair-unf Fos₂'
... | ft₂ , os₂'' , FTft₂ , prf , Fos₂'' =
  helper Bb Fos₁' s' ft₂ os₂'' FTft₂ Fos₂'' prf
