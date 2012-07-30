-- The BUILTIN pragma works with imported modules.

module Issue3Nat.B where

open import Issue3Nat.A

{-# BUILTIN NATURAL ℕ     #-}
{-# BUILTIN ZERO    zero  #-}
{-# BUILTIN SUC     succ  #-}

foo : ℕ → ℕ
foo n = 10
