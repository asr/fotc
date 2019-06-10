------------------------------------------------------------------------------
-- Conversion rules for the nest function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module CombinedFOT.FOTC.Program.Nest.ConversionRules where

open import CombinedFOT.FOTC.Program.Nest.NestConditional

open import Combined.FOTC.Base

------------------------------------------------------------------------------

postulate nest-0 : nest zero ≡ zero
{-# ATP prove nest-0 #-}

postulate nest-S : ∀ n → nest (succ₁ n) ≡ nest (nest n)
{-# ATP prove nest-S #-}
