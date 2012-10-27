------------------------------------------------------------------------------
-- Testing an alternative definition of subtraction
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.SubtractionSL where

open import Data.Nat hiding ( _∸_ )
open import Relation.Binary.PropositionalEquality

-- First definition (from the standard library).
_∸₁_ : ℕ → ℕ → ℕ
m     ∸₁ zero  = m
zero  ∸₁ suc n = zero
suc m ∸₁ suc n = m ∸₁ n

-- Second definition.
_∸₂_ : ℕ → ℕ → ℕ
m     ∸₂ zero  = m
zero  ∸₂ n     = zero
suc m ∸₂ suc n = m ∸₂ n

-- Both definitions are equivalents.
thm : ∀ m n → m ∸₁ n ≡ m ∸₂ n
thm m       zero    = refl
thm zero    (suc n) = refl
thm (suc m) (suc n) = thm m n