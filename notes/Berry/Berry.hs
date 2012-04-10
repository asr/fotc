-- Tested by GHC 7.4.1.

{-# LANGUAGE UnicodeSyntax #-}

-- From: Herbert P. Sander. A logic of functional programs with an
-- application to concurrency. PhD thesis, Chalmers University of
-- Technology and University of Gothenburg, Department of Computer
-- Sciences, 1992. pp. 12-13.

data Nat = Zero | Succ Nat
           deriving Show

loop ∷ a
loop = loop

-- Warning: Pattern match(es) are non-exhaustive
--          In an equation for `f':
--          Patterns not matched:
--            Zero (Succ (Succ _)) _
--            Zero Zero Zero
--            Zero Zero (Succ (Succ _))
--            (Succ (Succ _)) (Succ _) _
--            ...

f ∷ Nat → Nat → Nat → Nat
f Zero        (Succ Zero) _           = Succ Zero
f (Succ Zero) _           Zero        = Succ (Succ Zero)
f _           Zero        (Succ Zero) = Succ (Succ (Succ Zero))

-- Tests:
-- f Zero        (Succ Zero) loop = Succ Zero
-- f (Succ Zero) loop Zero        = Succ (Succ Zero)
-- f loop        Zero (Succ Zero) = *** Non-terminating ***
