------------------------------------------------------------------------------
-- FOTC natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.Nat where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat.Type public

infixl 7 _*_
infixl 6 _+_ _∸_

------------------------------------------------------------------------------
-- Arithmetic operations

postulate
  _+_  : D → D → D
  +-0x : ∀ n → zero + n      ≡ n
  +-Sx : ∀ m n → succ₁ m + n ≡ succ₁ (m + n)
{-# ATP axioms +-0x +-Sx #-}

postulate
  _∸_  : D → D → D
  ∸-x0 : ∀ n → n ∸ zero      ≡ n
  ∸-xS : ∀ m n → m ∸ succ₁ n ≡ pred₁ (m ∸ n)
{-# ATP axioms ∸-x0 ∸-xS #-}

postulate
  _*_  : D → D → D
  *-0x : ∀ n → zero * n      ≡ zero
  *-Sx : ∀ m n → succ₁ m * n ≡ n + m * n
{-# ATP axioms *-0x *-Sx #-}
