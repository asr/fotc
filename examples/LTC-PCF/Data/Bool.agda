------------------------------------------------------------------------------
-- The Booleans
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Bool where

open import LTC-PCF.Base

-- We add 3 to the fixities of the standard library.
infixr 9 _&&_

------------------------------------------------------------------------------
-- The LTC-PCF Booleans type (inductive predicate for total Booleans).
open import LTC-PCF.Data.Bool.Type public

------------------------------------------------------------------------------
-- Basic functions

-- The conjunction.
_&&_  : D → D → D
a && b = if a then b else false

-- The negation.
not : D → D
not b = if b then false else true
