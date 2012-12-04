{-# LANGUAGE UnicodeSyntax #-}

data Nat = Z | S Nat

instance Eq Nat where
  Z   == Z   = True
  S m == S n = m == n
  _   == _   = False

iter₀ ∷ (Nat → Nat) → Nat → [Nat]
iter₀ f n = if n == Z then [] else n : iter₀ f (f n)
