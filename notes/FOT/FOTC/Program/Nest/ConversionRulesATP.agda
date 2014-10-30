------------------------------------------------------------------------------
-- Conversion rules for the nest function
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Program.Nest.ConversionRulesATP where

open import FOT.FOTC.Program.Nest.NestConditional

open import FOTC.Base

------------------------------------------------------------------------------

postulate nest-0 : nest zero ≡ zero
{-# ATP prove nest-0 #-}

postulate nest-S : ∀ n → nest (succ₁ n) ≡ nest (nest n)
{-# ATP prove nest-S #-}
