{-# LANGUAGE UnicodeSyntax #-}

module Rec where

-- The definition of rec in LTC-PCF requires a fixed-point operator of
-- type
--
-- fix : ((D → D) → D → D) → D → D
--
-- instead of
--
-- fix : (D → D) → D.

import Data.Peano ( PeanoNat(S,Z) )

type T = PeanoNat → PeanoNat → (PeanoNat → PeanoNat → PeanoNat) → PeanoNat

rec0 ∷ T
rec0 Z     a _ = a
rec0 (S n) a f = f n (rec0 n a f)

rec1 ∷ T
rec1 n a f = if n == Z then a else f n (rec0 n a f)

fix1 ∷ (T → T) → T
fix1 f = f (fix1 f)

-- Doesn't work!
fix2 ∷ (PeanoNat → PeanoNat) → PeanoNat
fix2 f = f (fix2 f)

rech ∷ T → T
rech r n a f = if n == Z then a else f n (r n a f)

rec2 ∷ T
rec2 = fix1 rech
