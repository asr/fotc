------------------------------------------------------------------------------
-- Even predicate
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with FOT on 08 March 2012.

module Draft.FOTC.Data.Nat.Even where

open import FOTC.Base

------------------------------------------------------------------------------

data Even : D → Set where
  zE :                  Even zero
  nE : ∀ {d} → Even d → Even (succ₁ (succ₁ d))

Even-ind : (A : D → Set) →
          A zero →
          (∀ {d} → A d → A (succ₁ (succ₁ d))) →
          ∀ {d} → Even d → A d
Even-ind A A0 h zE      = A0
Even-ind A A0 h (nE Ed) = h (Even-ind A A0 h Ed)
