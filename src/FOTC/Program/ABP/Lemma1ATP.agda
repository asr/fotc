------------------------------------------------------------------------------
-- ABP lemma 1
------------------------------------------------------------------------------

-- From the paper: The first lemma states that given a start state Abp
-- (of the alternating bit protocol) we will arrive at a state Abp',
-- where the message has been received by the receiver, but where the
-- acknowledgement has not yet been received by the sender.

module FOTC.Program.ABP.Lemma1ATP where

open import FOTC.Base

open import FOTC.Data.List

open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Lemma1ATP.Helper
open import FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

-- From the paper: From the assumption that os₀ ∈ Fair, and hence by
-- unfolding Fair we conclude that there are ol₀ : O*L and os₀' :
-- Fair, such that
--
-- os₀ = ol₀ ++ os₀'.
--
-- We proceed by induction on ol₀ : O*L using lemma₁-helper.
lemma₁ : ∀ {b i' is' os₀ os₁ as bs cs ds js} →
         Bit b →
         Fair os₀ →
         Fair os₁ →
         Abp b (i' ∷ is') os₀ os₁ as bs cs ds js →
         ∃ λ os₀' → ∃ λ os₁' →
         ∃ λ as' → ∃ λ bs' → ∃ λ cs' → ∃ λ ds' → ∃ λ js' →
         Fair os₀'
         ∧ Fair os₁'
         ∧ Abp' b i' is' os₀' os₁' as' bs' cs' ds' js'
         ∧ js ≡ i' ∷ js'
lemma₁ {os₀ = os₀} Bb Fos₀ Fos₁ h = helper Bb Fos₁ h OLol₀ Fos₀' os₀-eq
  where
  unfold-os₀ : ∃ λ ol₀ → ∃ λ os₀' → O*L ol₀ ∧ Fair os₀' ∧ os₀ ≡ ol₀ ++ os₀'
  unfold-os₀ = Fair-gfp₁ Fos₀

  ol₀ : D
  ol₀ = ∃-proj₁ unfold-os₀

  os₀' : D
  os₀' = ∃-proj₁ (∃-proj₂ unfold-os₀)

  OLol₀ : O*L ol₀
  OLol₀ = ∧-proj₁ (∃-proj₂ (∃-proj₂ unfold-os₀))

  Fos₀' : Fair os₀'
  Fos₀' = ∧-proj₁ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-os₀)))

  os₀-eq : os₀ ≡ ol₀ ++ os₀'
  os₀-eq = ∧-proj₂ (∧-proj₂ (∃-proj₂ (∃-proj₂ unfold-os₀)))
