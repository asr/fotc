------------------------------------------------------------------------------
-- ABP terms
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.ABP.Terms where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.Loop
open import Interactive.FOTC.Data.Bool

------------------------------------------------------------------------------
-- N.B. We did not define @Bit = Bool@ due to the issue #11.
Bit : D → Set
Bit b = Bool b

F T : D
F = false
T = true

postulate
  <_,_> : D → D → D
  ok    : D → D
