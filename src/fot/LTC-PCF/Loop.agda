------------------------------------------------------------------------------
-- A looping (error) combinator
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LTC-PCF.Loop where

open import LTC-PCF.Base

------------------------------------------------------------------------------

error : D
error = fix (λ f → f)
