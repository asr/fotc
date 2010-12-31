------------------------------------------------------------------------------
-- PA propositional equality
------------------------------------------------------------------------------

module AxiomaticPA.Relation.Binary.PropositionalEqualityATP where

open import AxiomaticPA.Base

------------------------------------------------------------------------------
-- Identity properties

postulate
  refl : ∀ {n} → n ≣ n
{-# ATP prove refl #-}

postulate
  sym : ∀ {m n} → m ≣ n → n ≣ m
{-# ATP prove sym #-}

postulate
  trans : ∀ {m n o} → m ≣ n → n ≣ o → m ≣ o
{-# ATP prove trans #-}
