------------------------------------------------------------------------------
-- LTC natural numbers
------------------------------------------------------------------------------

module LTC.Data.Nat where

open import LTC.Base

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infixl 9  _+_ _-_

------------------------------------------------------------------------------
-- The LTC natural numbers type.
open import LTC.Data.Nat.Type public

------------------------------------------------------------------------------
-- Arithmetic operations

postulate
  _+_  : D → D → D
  +-0x : (d : D) →   zero   + d ≡ d
  +-Sx : (d e : D) → succ d + e ≡ succ (d + e)
{-# ATP axiom +-0x #-}
{-# ATP axiom +-Sx #-}

postulate
  _-_      : D → D → D
  minus-x0 : (d : D) →   d      - zero   ≡ d
  minus-0S : (d : D) →   zero   - succ d ≡ zero
  minus-SS : (d e : D) → succ d - succ e ≡ d - e
{-# ATP axiom minus-x0 #-}
{-# ATP axiom minus-0S #-}
{-# ATP axiom minus-SS #-}

postulate
  _*_ : D → D → D
  *-0x : (d : D) →   zero   * d ≡ zero
  *-Sx : (d e : D) → succ d * e ≡ e + d * e
{-# ATP axiom *-0x #-}
{-# ATP axiom *-Sx #-}
