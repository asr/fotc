------------------------------------------------------------------------------
-- The McCarthy 91 function: A function with nested recursion
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.McCarthy91.McCarthy91 where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- The McCarthy 91 function.
postulate
  f₉₁    : D → D
  f₉₁-eq : ∀ n → f₉₁ n ≡ (if (gt n 100') then n ∸ 10' else f₉₁ (f₉₁ (n + 11')))
{-# ATP axiom f₉₁-eq #-}
