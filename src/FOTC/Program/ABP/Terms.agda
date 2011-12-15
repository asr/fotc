------------------------------------------------------------------------------
-- ABP terms
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Terms where

open import FOTC.Base
open import FOTC.Data.Bool

------------------------------------------------------------------------------
-- We use 'Stream' instead of 'Inf'.

Bit : D → Set
Bit b = Bool b
{-# ATP definition Bit #-}

O : D
O = false
{-# ATP definition O #-}

L : D
L = true
{-# ATP definition L #-}

error : D
error = loop

postulate
  <_,_> : D → D → D
  ok    : D → D
