------------------------------------------------------------------------------
-- Co-inductive natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Conat where

open import FOTC.Base

-- The FOTC co-inductive natural numbers type (co-inductive predicate
-- for total co-inductive natural)
open import FOTC.Data.Conat.Type public

------------------------------------------------------------------------------

postulate
  ω    : D
  ω-eq : ω ≡ succ₁ ω
{-# ATP axiom ω-eq #-}
