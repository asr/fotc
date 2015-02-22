------------------------------------------------------------------------------
-- The Booleans
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Bool where

open import FOTC.Base
open import FOTC.Data.Bool.Type public

infixr 6 _&&_

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
