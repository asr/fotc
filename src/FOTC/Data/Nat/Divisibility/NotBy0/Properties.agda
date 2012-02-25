------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Divisibility.NotBy0.Properties where

open import Common.Function

open import FOTC.Base
open import FOTC.Base.Properties
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility.NotBy0

------------------------------------------------------------------------------
-- Any positive number divides 0.
S∣0 : ∀ {n} → N n → succ₁ n ∣ zero
S∣0 {n} Nn = S≠0 , zero ,, zN , sym (*-0x (succ₁ n))

-- 0 doesn't divide any number.
0∤x : ∀ {n} → ¬ (zero ∣ n)
0∤x (0≠0 , _) = ⊥-elim $ 0≠0 refl
