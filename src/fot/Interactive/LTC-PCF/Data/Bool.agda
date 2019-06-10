------------------------------------------------------------------------------
-- The Booleans
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.LTC-PCF.Data.Bool where

open import Interactive.LTC-PCF.Base
open import Interactive.LTC-PCF.Data.Bool.Type public

infixr 6 _&&_

------------------------------------------------------------------------------
-- Basic functions

-- The conjunction.
_&&_  : D → D → D
a && b = if a then b else false

-- The negation.
not : D → D
not b = if b then false else true
