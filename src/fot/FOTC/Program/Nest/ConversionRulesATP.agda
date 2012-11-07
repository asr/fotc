------------------------------------------------------------------------------
-- Conversion rules for the nest function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Nest.ConversionRulesATP where

open import FOTC.Base
open import FOTC.Program.Nest.Nest

------------------------------------------------------------------------------
-- The conversion rules are not required.

private
  postulate nest-0 : nest zero ≡ zero
  {-# ATP prove nest-0 #-}

  postulate nest-S : ∀ n → nest (succ₁ n) ≡ nest (nest n)
  {-# ATP prove nest-S #-}
