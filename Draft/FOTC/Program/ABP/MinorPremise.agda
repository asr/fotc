------------------------------------------------------------------------------
-- ABP minor premise
------------------------------------------------------------------------------

module Draft.FOTC.Program.ABP.MinorPremise where

open import FOTC.Base

open import Draft.FOTC.Program.ABP.ABP

------------------------------------------------------------------------------

-- The relation _B_ is a post-fixed point of the bisimilarity functor
-- (see FOTC.Relation.Binary.Bisimilarity). The paper calls it the
-- minor premise.

-- From the paper: The proof of the minor premise uses two lemmas. The
-- first lemma (lemma₁) states that given a start state Abp (of the
-- alternating bit protocol) we will arrive at a state Abp', where the
-- message has been received by the receiver, but where the
-- acknowledgement has not yet been received by the sender. The second
-- lemma (lemma₂) states that given a state of the latter kind we will
-- arrive at a new start state, which is identical to the old start
-- state except that the bit has alternated and the first item in the
-- input stream has been removed.

postulate
  minorPremise : ∀ {is js} → is B js →
                 ∃ λ i' → ∃ λ is' → ∃ λ js' →
                 is' B js' ∧ is ≡ i' ∷ is' ∧ js ≡ i' ∷ js'
