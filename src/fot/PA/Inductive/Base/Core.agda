------------------------------------------------------------------------------
-- The inductive PA universe
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This file contains some core definitions which are reexported by
-- PA.Inductive.Base.

module PA.Inductive.Base.Core where

-- PA universe.
--
-- We chose the symbol M because there are non-standard models of
-- Peano Arithmetic, where the domain is not the set of natural
-- numbers.
data M : Set where
  zero :     M
  succ : M → M
