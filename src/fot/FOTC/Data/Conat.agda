------------------------------------------------------------------------------
-- Co-inductive natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Conat where

open import FOTC.Base
open import FOTC.Data.Conat.Type public

------------------------------------------------------------------------------

postulate
  ∞    : D
  ∞-eq : ∞ ≡ succ₁ ∞
{-# ATP axiom ∞-eq #-}
