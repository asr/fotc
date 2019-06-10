------------------------------------------------------------------------------
-- ABP terms
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.ABP.Terms where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.Loop
open import Combined.FOTC.Data.Bool

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
