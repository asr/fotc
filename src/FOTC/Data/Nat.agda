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
-- The FOTC natural numbers type (inductive predicate for the total
-- natural numbers).
open import FOTC.Data.Nat.Type public

------------------------------------------------------------------------------
-- Arithmetic operations

postulate
  _+_  : D → D → D
  +-0x : ∀ n →   zero    + n ≡ n
  +-Sx : ∀ m n → succ₁ m + n ≡ succ₁ (m + n)
{-# ATP axiom +-0x +-Sx #-}

postulate
  _∸_  : D → D → D
  ∸-x0 : ∀ n →   n       ∸ zero    ≡ n
  ∸-0S : ∀ n →   zero    ∸ succ₁ n ≡ zero
  ∸-SS : ∀ m n → succ₁ m ∸ succ₁ n ≡ m ∸ n
{-# ATP axiom ∸-x0 ∸-0S ∸-SS #-}

postulate
  _*_  : D → D → D
  *-0x : ∀ n →   zero    * n ≡ zero
  *-Sx : ∀ m n → succ₁ m * n ≡ n + m * n
{-# ATP axiom *-0x *-Sx #-}
