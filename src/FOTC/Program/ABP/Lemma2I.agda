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
open import Common.Function

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.List
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.PropertiesI
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Helper function for the ABP lemma 2

module Helper where

  helper : ∀ {b i' is' fs₀' fs₁' as' bs' cs' ds' js'} →
           Bit b →
           Fair fs₀' →
           ABP' b i' is' fs₀' fs₁' as' bs' cs' ds' js' →
           ∃[ ft₁ ] ∃[ fs₁'' ] F*T ft₁ ∧ Fair fs₁'' ∧ fs₁' ≡ ft₁ ++ fs₁'' →
           ∃[ fs₀'' ] ∃[ fs₁'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
           Fair fs₀''
           ∧ Fair fs₁''
           ∧ ABP (not b) is' fs₀'' fs₁'' as'' bs'' cs'' ds'' js'
  helper {b} {i'} {is'} {fs₀'} {fs₁'} {as'} {bs'} {cs'} {ds'} {js'}
         Bb Ffs₀' (ds'ABP' , as'ABP , bs'ABP' , cs'ABP' , js'ABP')
         (.(T ∷ []) , fs₁'' , nilF*T , Ffs₁'' , fs₁'-eq) =
         fs₀' , fs₁'' , as'' , bs'' , cs'' , ds''
         , Ffs₀' , Ffs₁''
         , as''-eq , bs''-eq ,  cs''-eq , refl , js'-eq

    where
    fs'₁-eq-helper : fs₁' ≡ T ∷ fs₁''
    fs'₁-eq-helper = fs₁'                 ≡⟨ fs₁'-eq ⟩
                     (true ∷ []) ++ fs₁'' ≡⟨ ++-∷ true [] fs₁'' ⟩
                     true ∷ [] ++ fs₁''   ≡⟨ cong (_∷_ true) (++-[] fs₁'') ⟩
                     true ∷ fs₁'' ∎

    ds'' : D
    ds'' = corrupt · fs₁'' · cs'

    ds'-eq : ds' ≡ ok b ∷ ds''
    ds'-eq =
      ds'
        ≡⟨ ds'ABP' ⟩
      corrupt · fs₁' · (b ∷ cs')
        ≡⟨ subst (λ t → corrupt · fs₁' · (b ∷ cs') ≡ corrupt · t · (b ∷ cs'))
                 fs'₁-eq-helper
                 refl
        ⟩
      corrupt · (T ∷ fs₁'') · (b ∷ cs')
        ≡⟨ corrupt-T fs₁'' b cs' ⟩
      ok b ∷ corrupt · fs₁'' · cs'
        ≡⟨ refl ⟩
      ok b ∷ ds'' ∎

    as'' : D
    as'' = as'

    as''-eq : as'' ≡ send · not b · is' · ds''
    as''-eq =
      as''                         ≡⟨ as'ABP ⟩
      await b i' is' ds'           ≡⟨ cong (await b i' is') ds'-eq ⟩
      await b i' is' (ok b ∷ ds'') ≡⟨ await-ok≡ b b i' is' ds'' refl ⟩
      send · not b · is' · ds'' ∎

    bs'' : D
    bs'' = bs'

    bs''-eq : bs'' ≡ corrupt · fs₀' · as'
    bs''-eq = bs'ABP'

    cs'' : D
    cs'' = cs'

    cs''-eq : cs'' ≡ ack · not b · bs'
    cs''-eq = cs'ABP'

    js'-eq : js' ≡ out · not b · bs''
    js'-eq = js'ABP'

  helper {b} {i'} {is'} {fs₀'} {fs₁'} {as'} {bs'} {cs'} {ds'} {js'}
         Bb Ffs₀' (ds'ABP' , as'ABP , bs'ABP' , cs'ABP' , js'ABP')
         (.(F ∷ ft₁) , fs₁'' , consF*T {ft₁} FTft₁ , Ffs₁'' , fs₁'-eq)
         = helper Bb (tail-Fair Ffs₀') ABP'IH (ft₁ , fs₁'' , FTft₁ , Ffs₁'' , refl)

    where
    fs₀⁵ : D
    fs₀⁵ = tail₁ fs₀'

    fs₁⁵ : D
    fs₁⁵ = ft₁ ++ fs₁''

    fs₁'-eq-helper : fs₁' ≡ F ∷ fs₁⁵
    fs₁'-eq-helper =
      fs₁'               ≡⟨ fs₁'-eq ⟩
      (F ∷ ft₁) ++ fs₁'' ≡⟨ ++-∷ _ _ _ ⟩
      F ∷ ft₁ ++ fs₁''   ≡⟨ refl ⟩
      F ∷ fs₁⁵ ∎

    ds⁵ : D
    ds⁵ = corrupt · fs₁⁵ · cs'

    ds'-eq : ds' ≡ error ∷ ds⁵
    ds'-eq =
      ds'
        ≡⟨ ds'ABP' ⟩
      corrupt · fs₁' · (b ∷ cs')
        ≡⟨ subst (λ t → corrupt · fs₁' · (b ∷ cs') ≡ corrupt · t · (b ∷ cs'))
                 fs₁'-eq-helper
                 refl
        ⟩
      corrupt · (F ∷ fs₁⁵) · (b ∷ cs')
        ≡⟨ corrupt-F _ _ _ ⟩
      error ∷ corrupt · fs₁⁵ · cs'
        ≡⟨ refl ⟩
      error ∷ ds⁵ ∎

    as⁵ : D
    as⁵ = await b i' is' ds⁵

    as'-eq : as' ≡ < i' , b > ∷ as⁵
    as'-eq =
      as'
        ≡⟨ as'ABP ⟩
      await b i' is' ds'
        ≡⟨ cong (await b i' is') ds'-eq ⟩
      await b i' is' (error ∷ ds⁵)
        ≡⟨ await-error _ _ _ _ ⟩
      < i' , b > ∷ await b i' is' ds⁵
        ≡⟨ refl ⟩
      < i' , b > ∷ as⁵ ∎

    bs⁵ : D
    bs⁵ = corrupt · fs₀⁵ · as⁵

    bs'-eq-helper₁ : fs₀' ≡ T ∷ tail₁ fs₀' → bs' ≡ ok < i' , b > ∷ bs⁵
    bs'-eq-helper₁ h =
      bs'
        ≡⟨ bs'ABP' ⟩
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
      ok < i' , b > ∷ bs⁵ ∎

    bs'-eq-helper₂ : fs₀' ≡ F ∷ tail₁ fs₀' → bs' ≡ error ∷ bs⁵
    bs'-eq-helper₂ h =
      bs'
        ≡⟨ bs'ABP' ⟩
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
      error ∷ bs⁵ ∎

    bs'-eq : bs' ≡ ok < i' , b > ∷ bs⁵ ∨ bs' ≡ error ∷ bs⁵
    bs'-eq = [ (λ h → inj₁ (bs'-eq-helper₁ h))
             , (λ h → inj₂ (bs'-eq-helper₂ h))
             ] (head-tail-Fair Ffs₀')

    cs⁵ : D
    cs⁵ = ack · not b · bs⁵

    cs'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs⁵ → cs' ≡ b ∷ cs⁵
    cs'-eq-helper₁ h =
      cs'
      ≡⟨ cs'ABP' ⟩
      ack · not b · bs'
        ≡⟨ subst (λ t → ack · not b · bs' ≡ ack · not b · t)
                 h
                 refl
        ⟩
      ack · not b · (ok < i' , b > ∷ bs⁵)
        ≡⟨ ack-ok≢ _ _ _ _ (not-x≢x Bb) ⟩
      not (not b) ∷ ack · not b · bs⁵
        ≡⟨ subst (λ t → not (not b) ∷ ack · not b · bs⁵ ≡
                        t           ∷ ack · not b · bs⁵)
                 (not² Bb)
                 refl
        ⟩
      b ∷ ack · not b · bs⁵
        ≡⟨ refl ⟩
      b ∷ cs⁵ ∎

    cs'-eq-helper₂ : bs' ≡ error ∷ bs⁵ → cs' ≡ b ∷ cs⁵
    cs'-eq-helper₂ h =
      cs'
        ≡⟨ cs'ABP' ⟩
      ack · not b · bs'
        ≡⟨ subst (λ t → ack · not b · bs' ≡ ack · not b · t)
                 h
                 refl
        ⟩
      ack · not b · (error ∷ bs⁵)
        ≡⟨ ack-error _ _ ⟩
      not (not b) ∷ ack · not b · bs⁵
        ≡⟨ subst (λ t → not (not b) ∷ ack · not b · bs⁵ ≡
                        t           ∷ ack · not b · bs⁵)
                 (not² Bb)
                 refl
        ⟩
      b ∷ ack · not b · bs⁵
        ≡⟨ refl ⟩
      b ∷ cs⁵ ∎

    cs'-eq : cs' ≡ b ∷ cs⁵
    cs'-eq = [ cs'-eq-helper₁ , cs'-eq-helper₂ ] bs'-eq

    js'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs⁵ → js' ≡ out · not b · bs⁵
    js'-eq-helper₁ h  =
      js'
        ≡⟨ js'ABP' ⟩
      out · not b · bs'
        ≡⟨ subst (λ t → out · not b · bs' ≡ out · not b · t)
                 h
                 refl
        ⟩
      out · not b · (ok < i' , b > ∷ bs⁵)
        ≡⟨ out-ok≢ (not b) b i' bs⁵ (not-x≢x Bb) ⟩
      out · not b · bs⁵ ∎

    js'-eq-helper₂ : bs' ≡ error ∷ bs⁵ → js' ≡ out · not b · bs⁵
    js'-eq-helper₂ h  =
      js'
        ≡⟨ js'ABP' ⟩
      out · not b · bs'
        ≡⟨ subst (λ t → out · not b · bs' ≡ out · not b · t)
                 h
                 refl
        ⟩
      out · not b · (error ∷ bs⁵)
        ≡⟨ out-error (not b) bs⁵ ⟩
      out · not b · bs⁵ ∎

    js'-eq : js' ≡ out · not b · bs⁵
    js'-eq = [ js'-eq-helper₁ , js'-eq-helper₂ ] bs'-eq

    ds⁵-eq : ds⁵ ≡ corrupt · fs₁⁵ · (b ∷ cs⁵)
    ds⁵-eq = trans refl (subst (λ t → corrupt · fs₁⁵ · cs' ≡ corrupt · fs₁⁵ · t )
                               cs'-eq
                               refl)

    ABP'IH : ABP' b i' is' fs₀⁵ fs₁⁵ as⁵ bs⁵ cs⁵ ds⁵ js'
    ABP'IH = ds⁵-eq , refl , refl , refl , js'-eq

------------------------------------------------------------------------------
-- From Dybjer and Sander's paper: From the assumption that fs₁ ∈
-- Fair, and hence by unfolding Fair we conclude that there are ft₁ :
-- F*T and fs₁'' : Fair, such that fs₁' = ft₁ ++ fs₁''.
--
-- We proceed by induction on ft₁ : F*T using helper.

open Helper
lemma₂ : ∀ {b i' is' fs₀' fs₁' as' bs' cs' ds' js'} →
         Bit b →
         Fair fs₀' →
         Fair fs₁' →
         ABP' b i' is' fs₀' fs₁' as' bs' cs' ds' js' →
         ∃[ fs₀'' ] ∃[ fs₁'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
         Fair fs₀''
         ∧ Fair fs₁''
         ∧ ABP (not b) is' fs₀'' fs₁'' as'' bs'' cs'' ds'' js'
lemma₂ Bb Ffs₀' Ffs₁' abp' = helper Bb Ffs₀' abp' (Fair-gfp₁ Ffs₁')
