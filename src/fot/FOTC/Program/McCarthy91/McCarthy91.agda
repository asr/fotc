------------------------------------------------------------------------------
-- The McCarthy 91 function: A function with nested recursion
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.McCarthy91.McCarthy91 where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- The McCarthy 91 function.
postulate
  f₉₁    : D → D
  f₉₁-eq : ∀ n → f₉₁ n ≡ (if (gt n 100') then n ∸ 10' else f₉₁ (f₉₁ (n + 11')))
{-# ATP axiom f₉₁-eq #-}
