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

module FOTC.Program.ABP.Lemma2ATP where

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.List
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Lemma2.HelperATP
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

-- From Dybjer and Sander's paper: From the assumption that os₁ ∈
-- Fair, and hence by unfolding Fair we conclude that there are ol₁ :
-- O*L and os₁'' : Fair, such that os₁' = ol₁ ++ os₁''.
--
-- We proceed by induction on ol₁ : O*L using lemma₂-helper.

lemma₂ : ∀ {b i' is' os₀' os₁' as' bs' cs' ds' js'} →
         Bit b →
         Fair os₀' →
         Fair os₁' →
         Abp' b i' is' os₀' os₁' as' bs' cs' ds' js' →
         ∃ λ os₀'' → ∃ λ os₁'' →
         ∃ λ as'' → ∃ λ bs'' → ∃ λ cs'' → ∃ λ ds'' →
         Fair os₀''
         ∧ Fair os₁''
         ∧ Abp (not b) is' os₀'' os₁'' as'' bs'' cs'' ds'' js'
lemma₂ {os₁' = os₁'} Bb Fos₀' Fos₁' h = helper Bb Fos₀' h OLol₀ Fos₁'' os₁'-eq
  where
  unfold-os₁' : ∃ λ ol₁ → ∃ λ os₁'' → O*L ol₁ ∧ Fair os₁'' ∧ os₁' ≡ ol₁ ++ os₁''
  unfold-os₁' = Fair-gfp₁ Fos₁'

  ol₁ : D
  ol₁ = ∃-proj₁ unfold-os₁'

  os₁'' : D
  os₁'' = ∃-proj₁ (∃-proj₂ unfold-os₁')

  OLol₀ : O*L ol₁
  OLol₀ = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold-os₁'))

  Fos₁'' : Fair os₁''
  Fos₁'' = ∧-proj₁ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-os₁')))

  os₁'-eq : os₁' ≡ ol₁ ++ os₁''
  os₁'-eq = ∧-proj₂ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-os₁')))
