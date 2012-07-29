-- The BUILTIN pragma works with imported modules.

module Nat.OtherModule where

open import Nat.Nat

{-# BUILTIN NATURAL ℕ     #-}
{-# BUILTIN ZERO    zero  #-}
{-# BUILTIN SUC     succ  #-}

foo : ℕ → ℕ
foo n = 10
