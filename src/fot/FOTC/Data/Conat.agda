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
  ω    : D
  ω-eq : ω ≡ succ₁ ω
{-# ATP axiom ω-eq #-}
