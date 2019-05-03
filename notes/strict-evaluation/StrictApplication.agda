{-# OPTIONS --exact-split    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --without-K      #-}

module StrictApplication where

open import Data.Nat

{-# NON_TERMINATING #-}
loop : ℕ
loop = loop

foo : ℕ
foo = (λ _ → 0) loop
