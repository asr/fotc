------------------------------------------------------------------------------
-- The McCarthy 91 function: A function with nested recursion
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.McCarthy91.McCarthy91 where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- The McCarthy 91 function.
postulate
  f₉₁    : D → D
  f₉₁-eq : ∀ n → f₉₁ n ≡ (if (gt n 100') then n ∸ 10' else f₉₁ (f₉₁ (n + 11')))
