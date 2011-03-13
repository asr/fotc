------------------------------------------------------------------------------
-- The inductive PA universe
------------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- PA.Inductive.Base.

module PA.Inductive.Base.Core where

-- PA universe.
data ℕ : Set where
  zero :     ℕ
  succ : ℕ → ℕ
