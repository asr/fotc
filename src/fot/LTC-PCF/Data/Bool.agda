------------------------------------------------------------------------------
-- The Booleans
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LTC-PCF.Data.Bool where

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Data/Bool.agda).
infixr 9 _&&_

open import LTC-PCF.Base
open import LTC-PCF.Data.Bool.Type public

------------------------------------------------------------------------------
-- Basic functions

-- The conjunction.
_&&_  : D → D → D
a && b = if a then b else false

-- The negation.
not : D → D
not b = if b then false else true
