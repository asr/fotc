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
  bs⁵ b i' is' ds fs₀⁵ = corrupt · fs₀⁵ · (as⁵ b i' is' ds)
  {-# ATP definition bs⁵ #-}

  cs⁵ : D → D → D → D → D → D
  cs⁵ b i' is' ds fs₀⁵ = ack · b · (bs⁵ b i' is' ds fs₀⁵)
  {-# ATP definition cs⁵ #-}

  ds⁵ : D → D → D → D → D → D → D
  ds⁵ b i' is' ds fs₀⁵ fs₁⁵ = corrupt · fs₁⁵ · cs⁵ b i' is' ds fs₀⁵
  {-# ATP definition ds⁵ #-}

  fs₀⁵ : D → D → D
  fs₀⁵ fs₀' ft₀⁵ = ft₀⁵ ++ fs₀'
  {-# ATP definition fs₀⁵ #-}

  fs₁⁵ : D → D
  fs₁⁵ fs₁ = tail₁ fs₁
  {-# ATP definition fs₁⁵ #-}

  helper : ∀ {b i' is' fs₀ fs₁ as bs cs ds js} →
           Bit b →
           Fair fs₁ →
           ABP b (i' ∷ is') fs₀ fs₁ as bs cs ds js →
           ∃[ ft₀ ] ∃[ fs₀' ] F*T ft₀ ∧ Fair fs₀' ∧ fs₀ ≡ ft₀ ++ fs₀' →
           ∃[ fs₀' ] ∃[ fs₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
           Fair fs₀'
           ∧ Fair fs₁'
           ∧ ABP' b i' is' fs₀' fs₁' as' bs' cs' ds' js'
           ∧ js ≡ i' ∷ js'
  helper {b} {i'} {is'} {js = js} Bb Ffs₁ abp
         (.(T ∷ []) , fs₀' , nilF*T , Ffs₀' , fs₀-eq) = prf
    where
    -- 25 July 2012: Only Equinox 5.0alpha (2010-06-29) proved the theorem (240 sec).
    postulate
      prf : ∃[ fs₀' ] ∃[ fs₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
            Fair fs₀'
            ∧ Fair fs₁'
            ∧ (ds' ≡ corrupt · fs₁' · (b ∷ cs')
              ∧ as' ≡ await b i' is' ds'
              ∧ bs' ≡ corrupt · fs₀' · as'
              ∧ cs' ≡ ack · not b · bs'
              ∧ js' ≡ out · not b · bs')
            ∧ js ≡ i' ∷ js'
    -- See issue #6.
    -- {-# ATP prove prf #-}
  helper {b} {i'} {is'} {fs₀} {fs₁} {as} {bs} {cs} {ds} {js} Bb Ffs₁ abp
         (.(F ∷ ft₀⁵) , fs₀' , fcons*T {ft₀⁵} FTft₀⁵ , Ffs₀' , fs₀-eq)
         = helper Bb (tail-Fair Ffs₁) ABPIH (ft₀⁵ , fs₀' , FTft₀⁵ , Ffs₀' , refl)
    where
    postulate fs₀-eq-helper : fs₀ ≡ F ∷ fs₀⁵ fs₀' ft₀⁵
    {-# ATP prove fs₀-eq-helper #-}

    postulate as-eq : as ≡ < i' , b > ∷ (as⁵ b i' is' ds)
    {-# ATP prove as-eq #-}

    postulate bs-eq : bs ≡ error ∷ (bs⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵))
    {-# ATP prove bs-eq fs₀-eq-helper as-eq #-}

    postulate cs-eq : cs ≡ not b ∷ cs⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵)
    {-# ATP prove cs-eq bs-eq #-}

    postulate
      ds-eq-helper₁ : fs₁ ≡ T ∷ tail₁ fs₁ →
                      ds ≡ ok (not b) ∷ ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁)
    {-# ATP prove ds-eq-helper₁ cs-eq #-}

    postulate
      ds-eq-helper₂ : fs₁ ≡ F ∷ tail₁ fs₁ →
                      ds ≡ error ∷ ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁)
    {-# ATP prove ds-eq-helper₂ cs-eq #-}

    ds-eq : ds ≡ ok (not b) ∷ ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁)
            ∨ ds ≡ error ∷ ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁)
    ds-eq = case (λ h → inj₁ (ds-eq-helper₁ h))
                 (λ h → inj₂ (ds-eq-helper₂ h))
                 (head-tail-Fair Ffs₁)

    postulate
      as⁵-eq-helper₁ : ds ≡ ok (not b) ∷ ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁) →
                       as⁵ b i' is' ds ≡
                       send · b · (i' ∷ is') · ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁)
    {-# ATP prove as⁵-eq-helper₁ x≢not-x #-}

    postulate
      as⁵-eq-helper₂ : ds ≡ error ∷ ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁) →
                       as⁵ b i' is' ds ≡
                       send · b · (i' ∷ is') · ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁)
    {-# ATP prove as⁵-eq-helper₂ #-}

    as⁵-eq : as⁵ b i' is' ds ≡
             send · b · (i' ∷ is') · ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁)
    as⁵-eq = case as⁵-eq-helper₁ as⁵-eq-helper₂ ds-eq

    postulate js-eq : js ≡ out · b · bs⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵)
    {-# ATP prove js-eq bs-eq #-}

    ABPIH : ABP b
                (i' ∷ is')
                (fs₀⁵ fs₀' ft₀⁵)
                (fs₁⁵ fs₁)
                (as⁵ b i' is' ds)
                (bs⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵))
                (cs⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵))
                (ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁))
                js
    ABPIH = as⁵-eq , refl , refl , refl , js-eq

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
         ABP b (i' ∷ is') fs₀ fs₁ as bs cs ds js →
         ∃[ fs₀' ] ∃[ fs₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
         Fair fs₀'
         ∧ Fair fs₁'
         ∧ ABP' b i' is' fs₀' fs₁' as' bs' cs' ds' js'
         ∧ js ≡ i' ∷ js'
lemma₁ Bb Ffs₀ Ffs₁ abp = helper Bb Ffs₁ abp (Fair-unf Ffs₀)
