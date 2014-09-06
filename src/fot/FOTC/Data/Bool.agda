------------------------------------------------------------------------------
-- The Booleans
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Bool where

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Data/Bool.agda).
infixr 9 _&&_

open import FOTC.Base
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
