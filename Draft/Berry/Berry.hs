{-# LANGUAGE UnicodeSyntax #-}

-- Tested by GHC 7.2.1.

-- From: Herbert P. Sander. A logic of functional programs with an
-- application to concurrency. PhD thesis, Chalmers University of
-- Technology and University of Gothenburg, Department of Computer
-- Sciences, 1992. pp. 12-13.

data Nat = Zero | Succ Nat
           deriving Show

loop ∷ a
loop = loop

f ∷ Nat → Nat → Nat → Nat
f Zero        (Succ Zero) x           = Succ Zero
f (Succ Zero) x           Zero        = Succ (Succ Zero)
f x           Zero        (Succ Zero) = Succ (Succ (Succ Zero))

-- Tests:
-- f (Succ Zero) loop Zero        = Succ Zero
-- f (Succ Zero) loop Zero        = Succ (Succ Zero)
-- f loop        Zero (Succ Zero) = *** Non-terminating ***
