------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

module AxiomaticPA.Equality.PropertiesATP where

open import AxiomaticPA.Base

------------------------------------------------------------------------------

postulate
  refl : ∀ n → n ≣ n
{-# ATP prove refl #-}

postulate
  sym : ∀ {m n} → m ≣ n → n ≣ m
{-# ATP prove sym #-}

postulate
  trans : ∀ {m n o} → m ≣ n → n ≣ o → m ≣ o
{-# ATP prove trans #-}
