{-# LANGUAGE UnicodeSyntax #-}

-- The definition of rec in LTC-PCF requires a fixed-point operator of
-- type
--
-- fix : ((D → D) → D → D) → D → D
--
-- instead of
--
-- fix : (D → D) → D.

import Data.Peano

type T = Nat → Nat → (Nat → Nat → Nat) → Nat

rec0 ∷ T
rec0 Zero     a _ = a
rec0 (Succ n) a f = f n (rec0 n a f)

rec1 ∷ T
rec1 n a f = if n == Zero then a else f n (rec0 n a f)

fix1 ∷ (T → T) → T
fix1 f = f (fix1 f)

-- Doesn't work!
fix2 ∷ (Nat → Nat) → Nat
fix2 f = f (fix2 f)

rech ∷ T → T
rech r n a f = if n == Zero then a else f n (r n a f)

rec2 ∷ T
rec2 = fix1 rech
