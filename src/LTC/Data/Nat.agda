------------------------------------------------------------------------------
-- LTC natural numbers
------------------------------------------------------------------------------

module LTC.Data.Nat where

open import LTC.Base

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infixl 9  _+_ _∸_

------------------------------------------------------------------------------
-- The LTC natural numbers type.
open import LTC.Data.Nat.Type public

------------------------------------------------------------------------------
-- Arithmetic operations

postulate
  _+_  : D → D → D
  +-0x : ∀ d →   zero   + d ≡ d
  +-Sx : ∀ d e → succ d + e ≡ succ (d + e)
{-# ATP axiom +-0x #-}
{-# ATP axiom +-Sx #-}

postulate
  _∸_      : D → D → D
  ∸-x0 : ∀ d →   d      ∸ zero   ≡ d
  ∸-0S : ∀ d →   zero   ∸ succ d ≡ zero
  ∸-SS : ∀ d e → succ d ∸ succ e ≡ d ∸ e
{-# ATP axiom ∸-x0 #-}
{-# ATP axiom ∸-0S #-}
{-# ATP axiom ∸-SS #-}

postulate
  _*_ : D → D → D
  *-0x : ∀ d →   zero   * d ≡ zero
  *-Sx : ∀ d e → succ d * e ≡ e + d * e
{-# ATP axiom *-0x #-}
{-# ATP axiom *-Sx #-}
