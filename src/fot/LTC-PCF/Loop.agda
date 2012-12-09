------------------------------------------------------------------------------
-- A looping (error) combinator
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Loop where

open import LTC-PCF.Base

------------------------------------------------------------------------------

error : D
error = fix (λ f → f)
