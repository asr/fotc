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
open import FOTC.Data.Bool.PropertiesATP
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

  as⁵ : ∀ b i' is' ds → D
  as⁵ b i' is' ds = await b i' is' ds
  {-# ATP definition as⁵ #-}

  bs⁵ : D → D → D → D → D → D
  bs⁵ b i' is' ds os₀⁵ = corrupt · os₀⁵ · (as⁵ b i' is' ds)
  {-# ATP definition bs⁵ #-}

  cs⁵ : D → D → D → D → D → D
  cs⁵ b i' is' ds os₀⁵ = ack · b · (bs⁵ b i' is' ds os₀⁵)
  {-# ATP definition cs⁵ #-}

  ds⁵ : D → D → D → D → D → D → D
  ds⁵ b i' is' ds os₀⁵ os₁⁵ = corrupt · os₁⁵ · cs⁵ b i' is' ds os₀⁵
  {-# ATP definition ds⁵ #-}

  os₀⁵ : D → D → D
  os₀⁵ os₀' ft₀⁵ = ft₀⁵ ++ os₀'
  {-# ATP definition os₀⁵ #-}

  os₁⁵ : D → D
  os₁⁵ os₁ = tail₁ os₁
  {-# ATP definition os₁⁵ #-}

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
         .(F ∷ ft₀⁵) os₀' (f*tcons {ft₀⁵} FTft₀⁵) Fos₀' os₀-eq
         = helper Bb (tail-Fair Fos₁) ABPIH ft₀⁵ os₀' FTft₀⁵ Fos₀' refl
    where
    postulate os₀-eq-helper : os₀ ≡ F ∷ os₀⁵ os₀' ft₀⁵
    {-# ATP prove os₀-eq-helper #-}

    postulate as-eq : as ≡ < i' , b > ∷ (as⁵ b i' is' ds)
    {-# ATP prove as-eq #-}

    postulate bs-eq : bs ≡ error ∷ (bs⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵))
    {-# ATP prove bs-eq os₀-eq-helper as-eq #-}

    postulate cs-eq : cs ≡ not b ∷ cs⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵)
    {-# ATP prove cs-eq bs-eq #-}

    postulate
      ds-eq-helper₁ : os₁ ≡ T ∷ tail₁ os₁ →
                      ds ≡ ok (not b) ∷ ds⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵) (os₁⁵ os₁)
    {-# ATP prove ds-eq-helper₁ cs-eq #-}

    postulate
      ds-eq-helper₂ : os₁ ≡ F ∷ tail₁ os₁ →
                      ds ≡ error ∷ ds⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵) (os₁⁵ os₁)
    {-# ATP prove ds-eq-helper₂ cs-eq #-}

    ds-eq : ds ≡ ok (not b) ∷ ds⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵) (os₁⁵ os₁)
            ∨ ds ≡ error ∷ ds⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵) (os₁⁵ os₁)
    ds-eq = case (λ h → inj₁ (ds-eq-helper₁ h))
                 (λ h → inj₂ (ds-eq-helper₂ h))
                 (head-tail-Fair Fos₁)

    postulate
      as⁵-eq-helper₁ : ds ≡ ok (not b) ∷ ds⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵) (os₁⁵ os₁) →
                       as⁵ b i' is' ds ≡
                       send · b · (i' ∷ is') · ds⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵) (os₁⁵ os₁)
    {-# ATP prove as⁵-eq-helper₁ x≢not-x #-}

    postulate
      as⁵-eq-helper₂ : ds ≡ error ∷ ds⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵) (os₁⁵ os₁) →
                       as⁵ b i' is' ds ≡
                       send · b · (i' ∷ is') · ds⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵) (os₁⁵ os₁)
    {-# ATP prove as⁵-eq-helper₂ #-}

    as⁵-eq : as⁵ b i' is' ds ≡
             send · b · (i' ∷ is') · ds⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵) (os₁⁵ os₁)
    as⁵-eq = case as⁵-eq-helper₁ as⁵-eq-helper₂ ds-eq

    postulate js-eq : js ≡ out · b · bs⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵)
    {-# ATP prove js-eq bs-eq #-}

    ABPIH : ABP b
                (i' ∷ is')
                (os₀⁵ os₀' ft₀⁵)
                (os₁⁵ os₁)
                (as⁵ b i' is' ds)
                (bs⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵))
                (cs⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵))
                (ds⁵ b i' is' ds (os₀⁵ os₀' ft₀⁵) (os₁⁵ os₁))
                js
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
lemma₁ Bb Fos₀ Fos₁ abp with Fair-unf Fos₀
... | ft , os₀' , FTft , h , Fos₀' = helper Bb Fos₁ abp ft os₀' FTft Fos₀' h
