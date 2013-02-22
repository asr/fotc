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
  ∞N    : D
  ∞N-eq : ∞N ≡ succ₁ ∞N
{-# ATP axiom ∞N-eq #-}
