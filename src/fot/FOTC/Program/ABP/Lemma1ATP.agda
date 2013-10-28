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

module FOTC.Program.ABP.Lemma1ATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.Loop
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesATP using ( x≢not-x )
open import FOTC.Data.List
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.PropertiesATP
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Helper function for the ABP lemma 1

module Helper where
  -- We have these definitions outside the where clause to keep them
  -- simple for the ATPs.

  as^ : ∀ b i' is' ds → D
  as^ b i' is' ds = await b i' is' ds
  {-# ATP definition as^ #-}

  bs^ : D → D → D → D → D → D
  bs^ b i' is' ds os₀^ = corrupt · os₀^ · (as^ b i' is' ds)
  {-# ATP definition bs^ #-}

  cs^ : D → D → D → D → D → D
  cs^ b i' is' ds os₀^ = ack · b · (bs^ b i' is' ds os₀^)
  {-# ATP definition cs^ #-}

  ds^ : D → D → D → D → D → D → D
  ds^ b i' is' ds os₀^ os₁^ = corrupt · os₁^ · cs^ b i' is' ds os₀^
  {-# ATP definition ds^ #-}

  os₀^ : D → D → D
  os₀^ os₀' ft₀^ = ft₀^ ++ os₀'
  {-# ATP definition os₀^ #-}

  os₁^ : D → D
  os₁^ os₁ = tail₁ os₁
  {-# ATP definition os₁^ #-}

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
  helper {b} {i'} {is'} {js = js} Bb Fos₁ abp .(T ∷ []) os₀' f*tnil Fos₀' os₀-eq = prf
    where
    postulate
      prf : ∃[ os₀' ] ∃[ os₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
            Fair os₀'
            ∧ Fair os₁'
            ∧ (ds' ≡ corrupt · os₁' · (b ∷ cs')
              ∧ as' ≡ await b i' is' ds'
              ∧ bs' ≡ corrupt · os₀' · as'
              ∧ cs' ≡ ack · not b · bs'
              ∧ js' ≡ out · not b · bs')
            ∧ js ≡ i' ∷ js'
    {-# ATP prove prf #-}
  helper {b} {i'} {is'} {os₀} {os₁} {as} {bs} {cs} {ds} {js} Bb Fos₁ abp
         .(F ∷ ft₀^) os₀' (f*tcons {ft₀^} FTft₀^) Fos₀' os₀-eq
         = helper Bb (tail-Fair Fos₁) ABPIH ft₀^ os₀' FTft₀^ Fos₀' refl
    where
    postulate os₀-eq-helper : os₀ ≡ F ∷ os₀^ os₀' ft₀^
    {-# ATP prove os₀-eq-helper #-}

    postulate as-eq : as ≡ < i' , b > ∷ (as^ b i' is' ds)
    {-# ATP prove as-eq #-}

    postulate bs-eq : bs ≡ error ∷ (bs^ b i' is' ds (os₀^ os₀' ft₀^))
    {-# ATP prove bs-eq os₀-eq-helper as-eq #-}

    postulate cs-eq : cs ≡ not b ∷ cs^ b i' is' ds (os₀^ os₀' ft₀^)
    {-# ATP prove cs-eq bs-eq #-}

    postulate
      ds-eq-helper₁ : os₁ ≡ T ∷ tail₁ os₁ →
                      ds ≡ ok (not b) ∷ ds^ b i' is' ds (os₀^ os₀' ft₀^) (os₁^ os₁)
    {-# ATP prove ds-eq-helper₁ cs-eq #-}

    postulate
      ds-eq-helper₂ : os₁ ≡ F ∷ tail₁ os₁ →
                      ds ≡ error ∷ ds^ b i' is' ds (os₀^ os₀' ft₀^) (os₁^ os₁)
    {-# ATP prove ds-eq-helper₂ cs-eq #-}

    ds-eq : ds ≡ ok (not b) ∷ ds^ b i' is' ds (os₀^ os₀' ft₀^) (os₁^ os₁)
            ∨ ds ≡ error ∷ ds^ b i' is' ds (os₀^ os₀' ft₀^) (os₁^ os₁)
    ds-eq = case (λ h → inj₁ (ds-eq-helper₁ h))
                 (λ h → inj₂ (ds-eq-helper₂ h))
                 (head-tail-Fair Fos₁)

    postulate
      as^-eq-helper₁ : ds ≡ ok (not b) ∷ ds^ b i' is' ds (os₀^ os₀' ft₀^) (os₁^ os₁) →
                       as^ b i' is' ds ≡
                       send · b · (i' ∷ is') · ds^ b i' is' ds (os₀^ os₀' ft₀^) (os₁^ os₁)
    {-# ATP prove as^-eq-helper₁ x≢not-x #-}

    postulate
      as^-eq-helper₂ : ds ≡ error ∷ ds^ b i' is' ds (os₀^ os₀' ft₀^) (os₁^ os₁) →
                       as^ b i' is' ds ≡
                       send · b · (i' ∷ is') · ds^ b i' is' ds (os₀^ os₀' ft₀^) (os₁^ os₁)
    {-# ATP prove as^-eq-helper₂ #-}

    as^-eq : as^ b i' is' ds ≡
             send · b · (i' ∷ is') · ds^ b i' is' ds (os₀^ os₀' ft₀^) (os₁^ os₁)
    as^-eq = case as^-eq-helper₁ as^-eq-helper₂ ds-eq

    postulate js-eq : js ≡ out · b · bs^ b i' is' ds (os₀^ os₀' ft₀^)
    {-# ATP prove js-eq bs-eq #-}

    ABPIH : ABP b
                (i' ∷ is')
                (os₀^ os₀' ft₀^)
                (os₁^ os₁)
                (as^ b i' is' ds)
                (bs^ b i' is' ds (os₀^ os₀' ft₀^))
                (cs^ b i' is' ds (os₀^ os₀' ft₀^))
                (ds^ b i' is' ds (os₀^ os₀' ft₀^) (os₁^ os₁))
                js
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
... | ft , os₀' , FTft , h , Fos₀' = helper Bb Fos₁ abp ft os₀' FTft Fos₀' h
