------------------------------------------------------------------------------
-- Helper function for the ABP lemma 2
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Lemma2.HelperATP where

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.List
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.PropertiesATP
open import FOTC.Program.ABP.Terms
open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

-- We have these TPTP definitions outside the where clause to keep
-- them simple for the ATPs.

ds⁵ : D → D → D
ds⁵ cs' os₁⁵ = corrupt · os₁⁵ · cs'
{-# ATP definition ds⁵ #-}

as⁵ : D → D → D → D → D → D
as⁵ b i' is' cs' os₁⁵ = await b i' is' (ds⁵ cs' os₁⁵)
{-# ATP definition as⁵ #-}

bs⁵ : D → D → D → D → D → D → D
bs⁵ b i' is' cs' os₀⁵ os₁⁵ = corrupt · os₀⁵ · as⁵ b i' is' cs' os₁⁵
{-# ATP definition bs⁵ #-}

cs⁵ : D → D → D → D → D → D → D
cs⁵ b i' is' cs' os₀⁵ os₁⁵ = abpack · (not b) · bs⁵ b i' is' cs' os₀⁵ os₁⁵
{-# ATP definition cs⁵ #-}

os₀⁵ : D → D
os₀⁵ os₀' = tail₁ os₀'
{-# ATP definition os₀⁵ #-}

os₁⁵ : D → D → D
os₁⁵ ol₁ os₁'' = ol₁ ++ os₁''
{-# ATP definition os₁⁵ #-}

helper : ∀ {b i' is' os₀' os₁' as' bs' cs' ds' js'} →
         Bit b →
         Fair os₀' →
         Abp' b i' is' os₀' os₁' as' bs' cs' ds' js' →
         ∀ {ol₁ os₁''-aux} →
         O*L ol₁ → Fair (os₁''-aux) → os₁' ≡ ol₁ ++ os₁''-aux →
         ∃ λ os₀'' → ∃ λ os₁'' →
         ∃ λ as'' → ∃ λ bs'' → ∃ λ cs'' → ∃ λ ds'' →
         Fair os₀''
         ∧ Fair os₁''
         ∧ Abp (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'

helper {b} {i'} {is'} {js' = js'} Bb Fos₀' h nilO*L Fos₁'' os₁'-eq = prf
  where
  postulate
    prf : ∃ λ os₀'' → ∃ λ os₁'' →
          ∃ λ as'' → ∃ λ bs'' → ∃ λ cs'' → ∃ λ ds'' →
          Fair os₀''
          ∧ Fair os₁''
          ∧ as'' ≡ abpsend · not b · is' · ds''
          ∧ bs'' ≡ corrupt · os₀'' · as''
          ∧ cs'' ≡ abpack · not b · bs''
          ∧ ds'' ≡ corrupt · os₁'' · cs''
          ∧ js' ≡ abpout · not b · bs''
  {-# ATP prove prf #-}

helper {b} {i'} {is'} {os₀'} {os₁'} {as'} {bs'} {cs'} {ds'} {js'}
       Bb Fos₀' abp'
       {os₁''-aux = os₁''} (consO*L ol₁ OLol₁)
       Fos₁'' os₁'-eq = helper Bb (tail-Fair Fos₀') Abp'IH OLol₁ Fos₁'' refl
  where
  postulate os₁'-eq-helper : os₁' ≡ O ∷ os₁⁵ ol₁ os₁''
  {-# ATP prove os₁'-eq-helper #-}

  postulate ds'-eq : ds' ≡ error ∷ ds⁵ cs' (os₁⁵ ol₁ os₁'')
  {-# ATP prove ds'-eq os₁'-eq-helper #-}

  postulate as'-eq : as' ≡ < i' , b > ∷ as⁵ b i' is' cs' (os₁⁵ ol₁ os₁'')
  {-# ATP prove as'-eq #-}

  postulate
    bs'-eq-helper₁ : os₀' ≡ L ∷ tail₁ os₀' →
                     bs' ≡ ok < i' , b > ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  {-# ATP prove bs'-eq-helper₁ as'-eq #-}

  postulate
    bs'-eq-helper₂ : os₀' ≡ O ∷ tail₁ os₀' →
                     bs' ≡ error ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  {-# ATP prove bs'-eq-helper₁ as'-eq #-}

  bs'-eq : bs' ≡ ok < i' , b > ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
           ∨ bs' ≡ error ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  bs'-eq = [ (λ h → inj₁ (bs'-eq-helper₁ h))
           , (λ h → inj₂ (bs'-eq-helper₂ h))
           ] (head-tail-Fair Fos₀')

  postulate
    cs'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'') →
                     cs' ≡ b ∷ cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  {-# ATP prove cs'-eq-helper₁ not-x≠x not² #-}

  postulate
    cs'-eq-helper₂ : bs' ≡ error ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'') →
                     cs' ≡ b ∷ cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  {-# ATP prove cs'-eq-helper₂ not² #-}

  cs'-eq : cs' ≡ b ∷ cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  cs'-eq = [ cs'-eq-helper₁ , cs'-eq-helper₂ ] bs'-eq

  postulate
    js'-eq-helper₁ : bs' ≡ ok < i' , b > ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'') →
                     js' ≡ abpout · (not b) · bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  {-# ATP prove js'-eq-helper₁ not-x≠x #-}

  postulate
    js'-eq-helper₂ : bs' ≡ error ∷ bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'') →
                     js' ≡ abpout · (not b) · bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  {-# ATP prove js'-eq-helper₂ #-}

  js'-eq : js' ≡ abpout · (not b) · bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁'')
  js'-eq = [ js'-eq-helper₁ , js'-eq-helper₂ ] bs'-eq

  postulate
    ds⁵-eq : ds⁵ cs' (os₁⁵ ol₁ os₁'') ≡
             corrupt · (os₁⁵ ol₁ os₁'') · (b ∷ cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁''))

  Abp'IH : Abp' b i' is'
                (os₀⁵ os₀')
                (os₁⁵ ol₁ os₁'')
                (as⁵ b i' is' cs' (os₁⁵ ol₁ os₁''))
                (bs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁''))
                (cs⁵ b i' is' cs' (os₀⁵ os₀') (os₁⁵ ol₁ os₁''))
                (ds⁵ cs' (os₁⁵ ol₁ os₁''))
                js'
  Abp'IH = ds⁵-eq , refl , refl , refl , js'-eq
