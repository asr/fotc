{-# LANGUAGE UnicodeSyntax #-}

data Nat = Z | S Nat

instance Eq Nat where
  Z   == Z   = True
  S m == S n = m == n
  _   == _   = False

instance Ord Nat where
  Z   `compare` Z   = EQ
  Z   `compare` S _ = LT
  S _ `compare` Z   = GT
  S m `compare` S n = m `compare` n

instance Num Nat where

  Z + n   = n
  S m + n = S (m + n)

  Z * _   = Z
  S m * n = n + m * n

  m   - Z   = m
  Z   - S _ = Z
  S m - S n = m - n

  abs _ = error "abs"

  signum _ = error "signum"

  fromInteger 0 = Z
  fromInteger n = S (fromInteger (n - 1))

nat2Integer ∷ Nat → Integer
nat2Integer Z     = 0
nat2Integer (S n) = 1 + nat2Integer n

instance Show Nat where
  show n  = show (nat2Integer n)

f₉₁ ∷ Nat → Nat
f₉₁ n | n > 100   = n - 10
      | otherwise = f₉₁ (f₉₁ (n + 11))
