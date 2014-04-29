{-# Language UnicodeSyntax #-}

import Prelude hiding ( ($!) )

loop ∷ Int
loop = loop

-- Strict application
($!) ∷ (a → b) → a → b
f $! x = x `seq` f x

-- Non-looping
foo ∷ Int
foo = (\_ → 0) loop

-- Looping
bar ∷ Int
bar = (\_ → 0) $! loop
