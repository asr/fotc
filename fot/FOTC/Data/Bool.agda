------------------------------------------------------------------------------
-- The Booleans
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Bool where

open import FOTC.Base

-- We add 3 to the fixities of the standard library.
infixr 9 _&&_

------------------------------------------------------------------------------
-- The FOTC Booleans type (inductive predicate for total Booleans).
open import FOTC.Data.Bool.Type public

------------------------------------------------------------------------------
-- Basic functions

-- The conjunction.
_&&_  : D → D → D
a && b = if a then b else false
{-# ATP definition _&&_ #-}

-- The negation.
not : D → D
not b = if b then false else true
{-# ATP definition not #-}
