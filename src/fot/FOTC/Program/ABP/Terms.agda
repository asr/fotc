------------------------------------------------------------------------------
-- ABP terms
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.Terms where

open import FOTC.Base
open import FOTC.Base.Loop
open import FOTC.Data.Bool

------------------------------------------------------------------------------

Bit : D → Set
Bit = Bool
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
