------------------------------------------------------------------------------
-- Co-inductive natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.Conat where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Conat.Type public

------------------------------------------------------------------------------

postulate
  ∞    : D
  ∞-eq : ∞ ≡ succ₁ ∞
