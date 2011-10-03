------------------------------------------------------------------------------
-- Conversion functions between inductive natural numbers and FOTC
-- natural numbers
------------------------------------------------------------------------------

-- Tested with Agda 2.2.11 on 03 October 2011.

module IJP where

postulate
  D : Set
  zero : D
  succ : D → D

------------------------------------------------------------------------------

-- The FOTC natural numbers type.
data N : D → Set where
  zN :               N zero
  sN : ∀ {n} → N n → N (succ n)

-- The inductive natural numbers.
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
