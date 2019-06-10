------------------------------------------------------------------------------
-- Co-inductive natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.Conat where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Conat.Type public

------------------------------------------------------------------------------

postulate
  ∞    : D
  ∞-eq : ∞ ≡ succ₁ ∞
{-# ATP axiom ∞-eq #-}
