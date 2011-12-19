------------------------------------------------------------------------------
-- Helper function for the ABP lemma 1
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Lemma1.HelperATP where

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.List
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.PropertiesATP
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

-- We have these TPTP definitions outside the where clause to keep
-- them simple for the ATPs.

as⁵ : ∀ b i' is' ds → D
as⁵ b i' is' ds = await b i' is' ds
{-# ATP definition as⁵ #-}

bs⁵ : D → D → D → D → D → D
bs⁵ b i' is' ds fs₀⁵ = corrupt · fs₀⁵ · (as⁵ b i' is' ds)
{-# ATP definition bs⁵ #-}

cs⁵ : D → D → D → D → D → D
cs⁵ b i' is' ds fs₀⁵ = abpack · b · (bs⁵ b i' is' ds fs₀⁵)
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
         Abp b (i' ∷ is') fs₀ fs₁ as bs cs ds js →
         ∀ {ft₀} → F*T ft₀ →
         ∀ {fs₀'-aux} → Fair fs₀'-aux → fs₀ ≡ ft₀ ++ fs₀'-aux →
         ∃[ fs₀' ] ∃[ fs₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
         Fair fs₀'
         ∧ Fair fs₁'
         ∧ Abp' b i' is' fs₀' fs₁' as' bs' cs' ds' js'
         ∧ js ≡ i' ∷ js'
helper {b} {i'} {is'} {js = js} Bb Ffs₁ h nilF*T Ffs₀' fs₀-eq = prf
  where
  postulate
    prf : ∃[ fs₀' ] ∃[ fs₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
          Fair fs₀'
          ∧ Fair fs₁'
          ∧ (ds' ≡ corrupt · fs₁' · (b ∷ cs')
             ∧ as' ≡ await b i' is' ds'
             ∧ bs' ≡ corrupt · fs₀' · as'
             ∧ cs' ≡ abpack · (not b) · bs'
             ∧ js' ≡ abpout · (not b) · bs')
          ∧ js ≡ i' ∷ js'
  {-# ATP prove prf #-}

helper {b} {i'} {is'} {fs₀} {fs₁} {as} {bs} {cs} {ds} {js}
       Bb Ffs₁ abp
       (consF*T {ft₀⁵} FTft₀⁵)
       {fs₀'-aux = fs₀'} Ffs₀' fs₀-eq =
         helper Bb (tail-Fair Ffs₁) AbpIH FTft₀⁵ Ffs₀' refl
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
  ds-eq = [ (λ h → inj₁ (ds-eq-helper₁ h))
          , (λ h → inj₂ (ds-eq-helper₂ h))
          ] (head-tail-Fair Ffs₁)

  postulate
    as⁵-eq-helper₁ : ds ≡ ok (not b) ∷ ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁) →
                     as⁵ b i' is' ds ≡
                     abpsend · b · (i' ∷ is') · ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁)
  {-# ATP prove as⁵-eq-helper₁ x≠not-x #-}

  postulate
    as⁵-eq-helper₂ : ds ≡ error ∷ ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁) →
                     as⁵ b i' is' ds ≡
                     abpsend · b · (i' ∷ is') · ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁)
  {-# ATP prove as⁵-eq-helper₂ #-}

  as⁵-eq : as⁵ b i' is' ds ≡
           abpsend · b · (i' ∷ is') · ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁)
  as⁵-eq = [ as⁵-eq-helper₁ , as⁵-eq-helper₂ ] ds-eq

  postulate js-eq : js ≡ abpout · b · bs⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵)
  {-# ATP prove js-eq bs-eq #-}

  AbpIH : Abp b
              (i' ∷ is')
              (fs₀⁵ fs₀' ft₀⁵)
              (fs₁⁵ fs₁)
              (as⁵ b i' is' ds)
              (bs⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵))
              (cs⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵))
              (ds⁵ b i' is' ds (fs₀⁵ fs₀' ft₀⁵) (fs₁⁵ fs₁))
              js
  AbpIH = as⁵-eq , refl , refl , refl , js-eq
