------------------------------------------------------------------------------
-- A looping combinator
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Loop where

open import LTC-PCF.Base

------------------------------------------------------------------------------

loop : D
loop = fix (λ f → f)
