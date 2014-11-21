------------------------------------------------------------------------------
-- ABP terms
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.ABP.Terms where

open import FOTC.Base
open import FOTC.Base.Loop
open import FOTC.Data.Bool

------------------------------------------------------------------------------
-- N.B. We did not define @Bit = Bool@ due to the issue #11.
Bit : D → Set
Bit b = Bool b
{-# ATP definition Bit #-}

F T : D
F = false
T = true
{-# ATP definition F T #-}

postulate
  <_,_> : D → D → D
  ok    : D → D
