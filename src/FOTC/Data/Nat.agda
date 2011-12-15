------------------------------------------------------------------------------
-- FOTC natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat where

open import FOTC.Base

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infixl 9  _+_ _∸_

------------------------------------------------------------------------------
-- The FOTC natural numbers type.
open import FOTC.Data.Nat.Type public

------------------------------------------------------------------------------
-- Arithmetic operations

postulate
  _+_  : D → D → D
  +-0x : ∀ d →   zero    + d ≡ d
  +-Sx : ∀ d e → succ₁ d + e ≡ succ₁ (d + e)
{-# ATP axiom +-0x +-Sx #-}

postulate
  _∸_  : D → D → D
  ∸-x0 : ∀ d →   d       ∸ zero    ≡ d
  ∸-0S : ∀ d →   zero    ∸ succ₁ d ≡ zero
  ∸-SS : ∀ d e → succ₁ d ∸ succ₁ e ≡ d ∸ e
{-# ATP axiom ∸-x0 ∸-0S ∸-SS #-}

postulate
  _*_  : D → D → D
  *-0x : ∀ d →   zero    * d ≡ zero
  *-Sx : ∀ d e → succ₁ d * e ≡ e + d * e
{-# ATP axiom *-0x *-Sx #-}
