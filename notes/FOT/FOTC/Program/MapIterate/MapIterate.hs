{-# LANGUAGE UnicodeSyntax #-}

map ∷ (a → b) → [a] → [b]
map _ []     = []
map f (x:xs) = f x : map f xs

iterate ∷ (a → a) → a → [a]
iterate f x = x : iterate f (f x)
