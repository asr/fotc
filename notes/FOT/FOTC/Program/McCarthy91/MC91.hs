{-# LANGUAGE UnicodeSyntax #-}

data Nat = Z | S Nat

mc91 ∷ Nat → Nat
mc91 n | n > 100   = n - 10
       | otherwise = mc91 (mc91 (n + 11))
