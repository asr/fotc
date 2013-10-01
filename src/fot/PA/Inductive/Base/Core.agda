------------------------------------------------------------------------------
-- The inductive PA universe
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This file contains some core definitions which are reexported by
-- PA.Inductive.Base.

module PA.Inductive.Base.Core where

-- PA universe.
data ℕ : Set where
  zero :     ℕ
  succ : ℕ → ℕ
