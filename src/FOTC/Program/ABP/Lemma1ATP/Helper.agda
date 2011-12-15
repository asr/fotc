------------------------------------------------------------------------------
-- Helper function for the ABP lemma 1
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Lemma1ATP.Helper where

open import FOTC.Base
open import FOTC.Data.Bool
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
bs⁵ b i' is' ds os₀⁵ = corrupt · os₀⁵ · (as⁵ b i' is' ds)
{-# ATP definition bs⁵ #-}

cs⁵ : D → D → D → D → D → D
cs⁵ b i' is' ds os₀⁵ = abpack · b · (bs⁵ b i' is' ds os₀⁵)
{-# ATP definition cs⁵ #-}

ds⁵ : D → D → D → D → D → D → D
ds⁵ b i' is' ds os₀⁵ os₁⁵ = corrupt · os₁⁵ · cs⁵ b i' is' ds os₀⁵
{-# ATP definition ds⁵ #-}

os₀⁵ : D → D → D
os₀⁵ os₀' ol₀⁵ = ol₀⁵ ++ os₀'
{-# ATP definition os₀⁵ #-}

os₁⁵ : D → D
os₁⁵ os₁ = tail₁ os₁
{-# ATP definition os₁⁵ #-}

helper : ∀ {b i' is' os₀ os₁ as bs cs ds js} →
           Bit b →
           Fair os₁ →
           Abp b (i' ∷ is') os₀ os₁ as bs cs ds js →
           ∀ {ol₀} → O*L ol₀ →
           ∀ {os₀'-aux} → Fair os₀'-aux → os₀ ≡ ol₀ ++ os₀'-aux →
           ∃ λ os₀' → ∃ λ os₁' →
           ∃ λ as' → ∃ λ bs' → ∃ λ cs' → ∃ λ ds' → ∃ λ js' →
           Fair os₀'
           ∧ Fair os₁'
           ∧ Abp' b i' is' os₀' os₁' as' bs' cs' ds' js'
           ∧ js ≡ i' ∷ js'
helper {b} {i'} {is'} {js = js} Bb Fos₁ h nilO*L Fos₀' os₀-eq = prf
  where
  postulate
    prf : ∃ λ os₀' → ∃ λ os₁' →
          ∃ λ as' → ∃ λ bs' → ∃ λ cs' → ∃ λ ds' → ∃ λ js' →
          Fair os₀'
          ∧ Fair os₁'
          ∧ (ds' ≡ corrupt · os₁' · (b ∷ cs')
             ∧ as' ≡ await b i' is' ds'
             ∧ bs' ≡ corrupt · os₀' · as'
             ∧ cs' ≡ abpack · (not b) · bs'
             ∧ js' ≡ abpout · (not b) · bs')
          ∧ js ≡ i' ∷ js'
  {-# ATP prove prf #-}

helper {b} {i'} {is'} {os₀} {os₁} {as} {bs} {cs} {ds} {js}
       Bb Fos₁ abp
       (consO*L ol₀⁵ OLol₀⁵)
       {os₀'-aux = os₀'} Fos₀' os₀-eq =
         helper Bb (tail-Fair Fos₁) AbpIH OLol₀⁵ Fos₀' refl
  where
  postulate os₀-eq-helper : os₀ ≡ O ∷ os₀⁵ os₀' ol₀⁵
  {-# ATP prove os₀-eq-helper #-}

  postulate as-eq : as ≡ < i' , b > ∷ (as⁵ b i' is' ds)
  {-# ATP prove as-eq #-}

  postulate bs-eq : bs ≡ error ∷ (bs⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵))
  {-# ATP prove bs-eq os₀-eq-helper as-eq #-}

  postulate cs-eq : cs ≡ not b ∷ cs⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵)
  {-# ATP prove cs-eq bs-eq #-}

  postulate
    ds-eq-helper₁ : os₁ ≡ L ∷ tail₁ os₁ →
                    ds ≡ ok (not b) ∷ ds⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵) (os₁⁵ os₁)
  {-# ATP prove ds-eq-helper₁ cs-eq #-}

  postulate
    ds-eq-helper₂ : os₁ ≡ O ∷ tail₁ os₁ →
                    ds ≡ error ∷ ds⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵) (os₁⁵ os₁)
  {-# ATP prove ds-eq-helper₂ cs-eq #-}

  ds-eq : ds ≡ ok (not b) ∷ ds⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵) (os₁⁵ os₁)
          ∨ ds ≡ error ∷ ds⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵) (os₁⁵ os₁)
  ds-eq = [ (λ h → inj₁ (ds-eq-helper₁ h))
          , (λ h → inj₂ (ds-eq-helper₂ h))
          ] (head-tail-Fair Fos₁)

  postulate
    as⁵-eq-helper₁ : ds ≡ ok (not b) ∷ ds⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵) (os₁⁵ os₁) →
                     as⁵ b i' is' ds ≡
                     abpsend · b · (i' ∷ is') · ds⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵) (os₁⁵ os₁)
  {- ATP prove as⁵-eq-helper₁ #-}

  postulate
    as⁵-eq-helper₂ : ds ≡ error ∷ ds⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵) (os₁⁵ os₁) →
                     as⁵ b i' is' ds ≡
                     abpsend · b · (i' ∷ is') · ds⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵) (os₁⁵ os₁)
  {- ATP prove as⁵-eq-helper₂ #-}

  as⁵-eq : as⁵ b i' is' ds ≡
           abpsend · b · (i' ∷ is') · ds⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵) (os₁⁵ os₁)
  as⁵-eq = [ as⁵-eq-helper₁ , as⁵-eq-helper₂ ] ds-eq

  postulate js-eq : js ≡ abpout · b · bs⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵)
  {-# ATP prove js-eq bs-eq #-}

  AbpIH : Abp b
              (i' ∷ is')
              (os₀⁵ os₀' ol₀⁵)
              (os₁⁵ os₁)
              (as⁵ b i' is' ds)
              (bs⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵))
              (cs⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵))
              (ds⁵ b i' is' ds (os₀⁵ os₀' ol₀⁵) (os₁⁵ os₁))
              js
  AbpIH = as⁵-eq , refl , refl , refl , js-eq
