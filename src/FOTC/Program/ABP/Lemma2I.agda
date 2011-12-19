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

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.List
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Lemma2.HelperI
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

-- From Dybjer and Sander's paper: From the assumption that fs₁ ∈
-- Fair, and hence by unfolding Fair we conclude that there are ft₁ :
-- F*T and fs₁'' : Fair, such that fs₁' = ft₁ ++ fs₁''.
--
-- We proceed by induction on ft₁ : F*T using lemma₂-helper.

lemma₂ : ∀ {b i' is' fs₀' fs₁' as' bs' cs' ds' js'} →
         Bit b →
         Fair fs₀' →
         Fair fs₁' →
         Abp' b i' is' fs₀' fs₁' as' bs' cs' ds' js' →
         ∃[ fs₀'' ] ∃[ fs₁'' ] ∃[ as'' ] ∃[ bs'' ] ∃[ cs'' ] ∃[ ds'' ]
         Fair fs₀''
         ∧ Fair fs₁''
         ∧ Abp (not b) is' fs₀'' fs₁'' as'' bs'' cs'' ds'' js'
lemma₂ {fs₁' = fs₁'} Bb Ffs₀' Ffs₁' h = helper Bb Ffs₀' h FTft₀ Ffs₁'' fs₁'-eq
  where
  unfold-fs₁' : ∃[ ft₁ ] ∃[ fs₁'' ] F*T ft₁ ∧ Fair fs₁'' ∧ fs₁' ≡ ft₁ ++ fs₁''
  unfold-fs₁' = Fair-gfp₁ Ffs₁'

  ft₁ : D
  ft₁ = ∃-proj₁ unfold-fs₁'

  fs₁'' : D
  fs₁'' = ∃-proj₁ (∃-proj₂ unfold-fs₁')

  FTft₀ : F*T ft₁
  FTft₀ = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold-fs₁'))

  Ffs₁'' : Fair fs₁''
  Ffs₁'' = ∧-proj₁ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-fs₁')))

  fs₁'-eq : fs₁' ≡ ft₁ ++ fs₁''
  fs₁'-eq = ∧-proj₂ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-fs₁')))
