------------------------------------------------------------------------------
-- PA propositional equality
------------------------------------------------------------------------------

module AxiomaticPA.Relation.Binary.PropositionalEqualityI where

open import AxiomaticPA.Base

------------------------------------------------------------------------------
-- Identity properties

refl : ∀ {n} → n ≣ n
refl {n} = S₁ (S₅ n) (S₅ n)
{-# ATP hint refl #-}

sym : ∀ {m n} → m ≣ n → n ≣ m
sym m≣n = S₁ m≣n refl
{-# ATP hint sym #-}

trans : ∀ {m n o} → m ≣ n → n ≣ o → m ≣ o
trans m≣n = S₁ (sym m≣n)
{-# ATP hint trans #-}
