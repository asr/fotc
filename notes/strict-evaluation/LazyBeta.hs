{-# Language UnicodeSyntax #-}

loop ∷ Int
loop = loop

foo ∷ Int
foo = (\_ → 0) loop

-- No looping ... foo loop = 0.
