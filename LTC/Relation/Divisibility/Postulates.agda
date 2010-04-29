------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

module LTC.Relation.Divisibility.Postulates where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Function.Arithmetic
open import LTC.Relation.Divisibility
open import LTC.Relation.Inequalities

------------------------------------------------------------------------------

postulate
  -- If 'x' divides 'y' and 'z' then 'x' divides 'y + z'.
  x∣y→x∣z→x∣y+z : {m n p : D} → N m → N n → N p →
                  m ∣ n → m ∣ p → m ∣ n + p

  -- If x divides y, and y is positive, then x ≤ y.
  x∣S→x≤S : {m n : D} → N m → N n → m ∣ (succ n) → LE m (succ n)
