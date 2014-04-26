module StrictApplication where

open import Data.Nat

{-# NO_TERMINATION_CHECK #-}
loop : ℕ
loop = loop

foo : ℕ
foo = (λ _ → 0) loop
