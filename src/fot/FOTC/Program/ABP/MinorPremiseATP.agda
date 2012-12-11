------------------------------------------------------------------------------
-- ABP minor premise
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.MinorPremiseATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.Lemma1ATP
open import FOTC.Program.ABP.Lemma2ATP

------------------------------------------------------------------------------

-- The relation B is a post-fixed point of the bisimilarity functional
-- (see FOTC.Relation.Binary.Bisimilarity). The paper calls it the
-- minor premise.

-- From Dybjer and Sander's paper: The proof of the minor premise uses
-- two lemmas. The first lemma (lemma₁) states that given a start
-- state ABP (of the alternating bit protocol) we will arrive at a
-- state ABP', where the message has been received by the receiver,
-- but where the acknowledgement has not yet been received by the
-- sender. The second lemma (lemma₂) states that given a state of the
-- latter kind we will arrive at a new start state, which is identical
-- to the old start state except that the bit has alternated and the
-- first item in the input stream has been removed.

-- 11 December 2012: Only Vampire 0.6 (revision 903) proved the
-- theorem (240 sec).
postulate minorPremise : ∀ {is js} → B is js →
                         ∃[ i' ] ∃[ is' ] ∃[ js' ]
                         B is' js' ∧ is ≡ i' ∷ is' ∧ js ≡ i' ∷ js'
{-# ATP prove minorPremise lemma₁ lemma₂ not-Bool #-}
