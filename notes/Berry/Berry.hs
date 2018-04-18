{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

{-# LANGUAGE UnicodeSyntax #-}

-- From: Herbert P. Sander. A logic of functional programs with an
-- application to concurrency. PhD thesis, Chalmers University of
-- Technology and University of Gothenburg, Department of Computer
-- Sciences, 1992. pp. 12-13.

module Berry where

import Data.Peano ( PeanoNat(S,Z) )

loop ∷ a
loop = loop

-- Warning: Pattern match(es) are non-exhaustive
--          In an equation for `f':
--          Patterns not matched:
--            Z (S (S _)) _
--            Z Z Z
--            Z Z (S (S _))
--            (S (S _)) (S _) _
--            ...

f ∷ PeanoNat → PeanoNat → PeanoNat → PeanoNat
f Z     (S Z) _     = S Z
f (S Z) _     Z     = S (S Z)
f _     Z     (S Z) = S (S (S Z))

-- Tests:
-- f Z        (S Z) loop = 1
-- f (S Z) loop Z        = 2
-- f loop        Z (S Z) = *** Non-terminating ***
