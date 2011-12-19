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

module FOTC.Program.ABP.Lemma1I where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Lemma1.HelperI
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

-- From Dybjer and Sander's paper: From the assumption that fs₀ ∈
-- Fair, and hence by unfolding Fair we conclude that there are ft₀ :
-- F*T and fs₀' : Fair, such that fs₀ = ft₀ ++ fs₀'.
--
-- We proceed by induction on ft₀ : F*T using lemma₁-helper.
lemma₁ : ∀ {b i' is' fs₀ fs₁ as bs cs ds js} →
         Bit b →
         Fair fs₀ →
         Fair fs₁ →
         Abp b (i' ∷ is') fs₀ fs₁ as bs cs ds js →
         ∃[ fs₀' ] ∃[ fs₁' ] ∃[ as' ] ∃[ bs' ] ∃[ cs' ] ∃[ ds' ] ∃[ js' ]
         Fair fs₀'
         ∧ Fair fs₁'
         ∧ Abp' b i' is' fs₀' fs₁' as' bs' cs' ds' js'
         ∧ js ≡ i' ∷ js'
lemma₁ {fs₀ = fs₀} Bb Ffs₀ Ffs₁ h = helper Bb Ffs₁ h FTft₀ Ffs₀' fs₀-eq
  where
  unfold-fs₀ : ∃[ ft₀ ] ∃[ fs₀' ] F*T ft₀ ∧ Fair fs₀' ∧ fs₀ ≡ ft₀ ++ fs₀'
  unfold-fs₀ = Fair-gfp₁ Ffs₀

  ft₀ : D
  ft₀ = ∃-proj₁ unfold-fs₀

  fs₀' : D
  fs₀' = ∃-proj₁ (∃-proj₂ unfold-fs₀)

  FTft₀ : F*T ft₀
  FTft₀ = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold-fs₀))

  Ffs₀' : Fair fs₀'
  Ffs₀' = ∧-proj₁ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-fs₀)))

  fs₀-eq : fs₀ ≡ ft₀ ++ fs₀'
  fs₀-eq = ∧-proj₂ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-fs₀)))
