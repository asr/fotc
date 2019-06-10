------------------------------------------------------------------------------
-- The inductive PA universe
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This file contains some core definitions which are reexported by
-- Combined.PA.Inductive.Base.

module Combined.PA.Inductive.Base.Core where

-- PA universe.
data ℕ : Set where
  zero :     ℕ
  succ : ℕ → ℕ
