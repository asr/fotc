------------------------------------------------------------------------------
-- Conversion functions between inductive natural numbers and LTC
-- natural numbers
------------------------------------------------------------------------------

module IJP where

open import LTC.Base

open import LTC.Data.Nat

------------------------------------------------------------------------------

data IN : Set where
  zeroIN : IN
  succIN : IN → IN

i : IN → D
i zeroIN     = zero
i (succIN n) = succ (i n)

j : (n : IN) → N (i n)
j zeroIN     = zN
j (succIN n) = sN (j n)

p : {n : D} → N n → IN
p zN      = zeroIN
p (sN Nn) = succIN (p Nn)
