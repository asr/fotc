------------------------------------------------------------------------------
-- The Booleans
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Bool where

open import LTC-PCF.Base

------------------------------------------------------------------------------
-- The LTC-PCF Booleans type (inductive predicate for total Booleans).
open import LTC-PCF.Data.Bool.Type public

------------------------------------------------------------------------------
-- Basic functions

-- The negation.
not : D → D
not x = if x then false else true
