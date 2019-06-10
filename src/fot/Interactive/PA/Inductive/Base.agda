------------------------------------------------------------------------------
-- Inductive Peano arithmetic base
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.PA.Inductive.Base where

infixl 7 _*_
infixl 6 _+_

------------------------------------------------------------------------------
-- PA universe
open import Interactive.PA.Inductive.Base.Core public

-- First-order logic (without equality)
--
open import Common.FOL.FOL public hiding ( _,_ ; ∃ )
-- 2012-04-24. Agda bug? Why it is necessary to use the modifier
-- @using@ in the following importation?
open import Interactive.PA.Inductive.Existential public using ( _,_ ; ∃ )

-- The induction principle on the PA universe
ℕ-ind : (A : ℕ → Set) → A zero → (∀ n → A n → A (succ n)) → ∀ n → A n
ℕ-ind A A0 h zero     = A0
ℕ-ind A A0 h (succ n) = h n (ℕ-ind A A0 h n)

-- The identity type on the PA universe
open import Interactive.PA.Inductive.Relation.Binary.PropositionalEquality public

-- PA primitive recursive functions
_+_ : ℕ → ℕ → ℕ
zero   + n = n
succ m + n = succ (m + n)

_*_ : ℕ → ℕ → ℕ
zero   * n = zero
succ m * n = n + m * n

------------------------------------------------------------------------------
-- ATPs helpers

-- Addition axioms
+-0x : ∀ n → zero + n ≡ n
+-0x n = refl

+-Sx : ∀ m n → succ m + n ≡ succ (m + n)
+-Sx m n = refl

-- Multiplication axioms
*-0x : ∀ n → zero * n ≡ zero
*-0x n = refl

*-Sx : ∀ m n → succ m * n ≡ n + m * n
*-Sx m n = refl
