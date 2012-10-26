------------------------------------------------------------------------------
-- ABP terms
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Terms where

open import FOTC.Base
open FOTC.Base.Loop
open import FOTC.Data.Bool

------------------------------------------------------------------------------
-- We use 'Stream' instead of 'Inf'.

Bit : D → Set
Bit b = Bool b
{-# ATP definition Bit #-}

F : D
F = false
{-# ATP definition F #-}

T : D
T = true
{-# ATP definition T #-}

error : D
error = loop

postulate
  <_,_> : D → D → D
  ok    : D → D
