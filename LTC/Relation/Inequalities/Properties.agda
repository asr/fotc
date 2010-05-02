------------------------------------------------------------------------------
-- Properties of the inequalities
------------------------------------------------------------------------------

module LTC.Relation.Inequalities.Properties where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.Properties
open import LTC.Relation.Inequalities
open import MyStdLib.Data.Sum
open import MyStdLib.Function

------------------------------------------------------------------------------

-- TODO: Why the ATP couldn't prove it?
-- postulate
--   x≥0 : (n : D) → N n → GE n zero
-- {-# ATP prove x≥0 zN sN #-}

x≥0 : {n : D} → N n → GE n zero
x≥0 zN          = lt-00
x≥0 (sN {n} Nn) = lt-S0 n
-- {-# ATP hint x≥0 #-}

¬0>x : {n : D} → N n → ¬ (GT zero n)
¬0>x Nn 0>n = ⊥-elim prf
  where
    postulate
      prf : ⊥
    {-# ATP prove prf x≥0 #-}

¬S≤0 : {d : D} → ¬ (LE (succ d) zero)
¬S≤0 Sx≤0 = ⊥-elim prf
  where
    postulate
      -- The proof uses the axiom true≠false
      prf : ⊥
    {-# ATP prove prf #-}

x>y∨x≤y : {m n : D} → N m → N n → GT m n ∨ LE m n
x>y∨x≤y zN          Nn          = inj₂ $ x≥0 Nn
x>y∨x≤y (sN {m} Nm) zN          = inj₁ $ lt-0S m
x>y∨x≤y (sN {m} Nm) (sN {n} Nn) = prf $ x>y∨x≤y Nm Nn
  where
    postulate
      prf : (GT m n) ∨ (LE m n) →
            GT (succ m) (succ n) ∨ LE (succ m) (succ n)
    {-# ATP prove prf #-}

¬x<x : {m : D} → N m → ¬ (LT m m)
¬x<x zN _ = ⊥-elim prf
  where
  postulate prf : ⊥
  {-# ATP prove prf #-}
¬x<x (sN {m} Nm) _ = ⊥-elim (prf (¬x<x Nm))
  where
  postulate prf : ¬ (LT m m) → ⊥
  {-# ATP prove prf #-}

x≤x+y : {m n : D} → N m → N n → LE m (m + n)
x≤x+y         zN          Nn = x≥0 (+-N zN Nn)
x≤x+y {n = n} (sN {m} Nm) Nn = prf (x≤x+y Nm Nn)
  where
  postulate prf : lt (m + n) m ≡ false →
                  lt (succ m + n) (succ m) ≡ false
