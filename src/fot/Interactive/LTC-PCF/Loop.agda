------------------------------------------------------------------------------
-- A looping (error) combinator
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.LTC-PCF.Loop where

open import Interactive.LTC-PCF.Base

------------------------------------------------------------------------------

error : D
error = fix (λ f → f)
