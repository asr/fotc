------------------------------------------------------------------------------
-- A looping combinator
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.FO-LTC-PCF.Loop where

open import Draft.FO-LTC-PCF.Base

------------------------------------------------------------------------------

loop : D
loop = fix (λ f → f)
