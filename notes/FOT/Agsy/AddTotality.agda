module AddTotality where

-- Tested with the development version of the standard library on
-- 11 June 2012.

open import Relation.Binary.PropositionalEquality

infixl 9 _+_

------------------------------------------------------------------------------

postulate
  D    : Set
  zero : D
  succ : D → D

data N : D → Set where
  zN :               N zero
  sN : ∀ {n} → N n → N (succ n)

postulate
  _+_  : D → D → D
  +-0x : ∀ d →   zero   + d ≡ d
  +-Sx : ∀ d e → succ d + e ≡ succ (d + e)

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {m} {n} Nm Nn = {!-c -m -t 20!}  -- No solution found at time out (20s).

+-N₁ : ∀ {m n} → N m → N n → N (m + n)
+-N₁ zN Nn = {!-m!}   -- No solution found

+-N₁ (sN Nm) Nn = {!-m!} -- No solution found.
