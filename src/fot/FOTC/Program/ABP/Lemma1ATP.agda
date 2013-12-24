------------------------------------------------------------------------------
-- ABP lemma 1
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From Dybjer and Sander's paper: The first lemma states that given a
-- start state S of the ABP, we will arrive at a state S', where the
-- message has been received by the receiver, but where the
-- acknowledgement has not yet been received by the sender.

module FOTC.Program.ABP.Lemma1ATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.Loop
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesATP using ( x≢not-x )
open import FOTC.Data.List
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair.Type
open import FOTC.Program.ABP.Fair.PropertiesATP
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------
-- Helper function for the ABP lemma 1

module Helper where
  -- 30 November 2013. If we don't have the following definitions
  -- outside the where clause, the ATPs cannot prove the theorems.

  as^ : ∀ b i' is' ds → D
  as^ b i' is' ds = await b i' is' ds
  {-# ATP definition as^ #-}

  bs^ : D → D → D → D → D → D
  bs^ b i' is' ds os₁^ = corrupt os₁^ · (as^ b i' is' ds)
  {-# ATP definition bs^ #-}

  cs^ : D → D → D → D → D → D
  cs^ b i' is' ds os₁^ = ack b · (bs^ b i' is' ds os₁^)
  {-# ATP definition cs^ #-}

  ds^ : D → D → D → D → D → D → D
  ds^ b i' is' ds os₁^ os₂^ = corrupt os₂^ · cs^ b i' is' ds os₁^
  {-# ATP definition ds^ #-}

  os₁^ : D → D → D
  os₁^ os₁' ft₁^ = ft₁^ ++ os₁'
  {-# ATP definition os₁^ #-}

  os₂^ : D → D
  os₂^ os₂ = tail₁ os₂
  {-# ATP definition os₂^ #-}

  helper : ∀ {b i' is' os₁ os₂ as bs cs ds js} →
           Bit b →
           Fair os₂ →
           S b (i' ∷ is') os₁ os₂ as bs cs ds js →
           ∀ ft₁ os₁' → F*T ft₁ → Fair os₁' → os₁ ≡ ft₁ ++ os₁' →
           ∃[ os₁' ] ∃[ os₂' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
             Fair os₁'
             ∧ Fair os₂'
             ∧ S' b i' is' os₁' os₂' as' bs' cs' ds' js'
             ∧ js ≡ i' ∷ js'
  helper {b} {i'} {is'} {js = js}
         Bb Fos₂ s .(T ∷ []) os₁' f*tnil Fos₁' os₁-eq = prf
    where
    postulate
      prf : ∃[ os₁' ] ∃[ os₂' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
              Fair os₁'
              ∧ Fair os₂'
              ∧ (as' ≡ await b i' is' ds'
                 ∧ bs' ≡ corrupt os₁' · as'
                 ∧ cs' ≡ ack (not b) · bs'
                 ∧ ds' ≡ corrupt os₂' · (b ∷ cs')
                 ∧ js' ≡ out (not b) · bs')
              ∧ js ≡ i' ∷ js'
    {-# ATP prove prf #-}
  helper {b} {i'} {is'} {os₁} {os₂} {as} {bs} {cs} {ds} {js} Bb Fos₂ s
         .(F ∷ ft₁^) os₁' (f*tcons {ft₁^} FTft₁^) Fos₁' os₁-eq =
         helper Bb (tail-Fair Fos₂) ihS ft₁^ os₁' FTft₁^ Fos₁' refl
    where
    postulate os₁-eq-helper : os₁ ≡ F ∷ os₁^ os₁' ft₁^
    {-# ATP prove os₁-eq-helper #-}

    postulate as-eq : as ≡ < i' , b > ∷ (as^ b i' is' ds)
    {-# ATP prove as-eq #-}

    postulate bs-eq : bs ≡ error ∷ (bs^ b i' is' ds (os₁^ os₁' ft₁^))
    {-# ATP prove bs-eq os₁-eq-helper as-eq #-}

    postulate cs-eq : cs ≡ not b ∷ cs^ b i' is' ds (os₁^ os₁' ft₁^)
    {-# ATP prove cs-eq bs-eq #-}

    postulate
      ds-eq-helper₁ :
        os₂ ≡ T ∷ tail₁ os₂ →
        ds ≡ ok (not b) ∷ ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂)
    {-# ATP prove ds-eq-helper₁ cs-eq #-}

    postulate
      ds-eq-helper₂ : os₂ ≡ F ∷ tail₁ os₂ →
                      ds ≡ error ∷ ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂)
    {-# ATP prove ds-eq-helper₂ cs-eq #-}

    ds-eq : ds ≡ ok (not b) ∷ ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂)
            ∨ ds ≡ error ∷ ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂)
    ds-eq = case (λ h → inj₁ (ds-eq-helper₁ h))
                 (λ h → inj₂ (ds-eq-helper₂ h))
                 (head-tail-Fair Fos₂)

    postulate
      as^-eq-helper₁ :
        ds ≡ ok (not b) ∷ ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂) →
        as^ b i' is' ds ≡
          send b · (i' ∷ is') · ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂)
    {-# ATP prove as^-eq-helper₁ x≢not-x #-}

    postulate
      as^-eq-helper₂ :
        ds ≡ error ∷ ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂) →
        as^ b i' is' ds ≡
          send b · (i' ∷ is') · ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂)
    {-# ATP prove as^-eq-helper₂ #-}

    as^-eq : as^ b i' is' ds ≡
             send b · (i' ∷ is') · ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂)
    as^-eq = case as^-eq-helper₁ as^-eq-helper₂ ds-eq

    postulate js-eq : js ≡ out b · bs^ b i' is' ds (os₁^ os₁' ft₁^)
    {-# ATP prove js-eq bs-eq #-}

    ihS : S b
            (i' ∷ is')
            (os₁^ os₁' ft₁^)
            (os₂^ os₂)
            (as^ b i' is' ds)
            (bs^ b i' is' ds (os₁^ os₁' ft₁^))
            (cs^ b i' is' ds (os₁^ os₁' ft₁^))
            (ds^ b i' is' ds (os₁^ os₁' ft₁^) (os₂^ os₂))
            js
    ihS = as^-eq , refl , refl , refl , js-eq

------------------------------------------------------------------------------
-- From Dybjer and Sander's paper: From the assumption that os₁ ∈ Fair
-- and hence by unfolding Fair, we conclude that there are ft₁ :  F*T
-- and os₁' : Fair, such that os₁ = ft₁ ++ os₁'.
--
-- We proceed by induction on ft₁ : F*T using helper.

open Helper
lemma₁ : ∀ {b i' is' os₁ os₂ as bs cs ds js} →
         Bit b →
         Fair os₁ →
         Fair os₂ →
         S b (i' ∷ is') os₁ os₂ as bs cs ds js →
         ∃[ os₁' ] ∃[ os₂' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
           Fair os₁'
           ∧ Fair os₂'
           ∧ S' b i' is' os₁' os₂' as' bs' cs' ds' js'
           ∧ js ≡ i' ∷ js'
lemma₁ Bb Fos₁ Fos₂ s with Fair-unf Fos₁
... | ft₁ , os₁' , FTft₁ , prf , Fos₁' =
  helper Bb Fos₂ s ft₁ os₁' FTft₁ Fos₁' prf
