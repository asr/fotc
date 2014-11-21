{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- From: Peter Dybjer. Comparing integrated and external logics of
-- functional programs. Science of Computer Programming, 14:59–79,
-- 1990

module Norm where

postulate Char : Set

data Atom : Set where
  True False : Atom
  Var        : Char → Atom

data Exp : Set where
  at : Atom → Exp
  if : Exp → Exp → Exp → Exp

-- Agda doesn't recognize the termination of the function.
{-# TERMINATING #-}
norm : Exp → Exp
norm (at a)              = at a
norm (if (at a) y z)     = if (at a) (norm y) (norm z)
norm (if (if u v w) y z) = norm (if u (if v y z) (if w y z))
