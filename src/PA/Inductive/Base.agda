------------------------------------------------------------------------------
-- Inductive Peano arithmetic base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Inductive.Base where

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infixl 9  _+_

------------------------------------------------------------------------------
-- PA universe
open import PA.Inductive.Base.Core public

-- FOL (without equality)
open import Common.FOL.FOL public using ( ¬_ )

-- The induction principle on the PA universe
PA-ind : (P : M → Set) → P zero → (∀ n → P n → P (succ n)) → ∀ n → P n
PA-ind P P0 h zero     = P0
PA-ind P P0 h (succ n) = h n (PA-ind P P0 h n)

-- The identity type on the PA universe
open import PA.Inductive.Relation.Binary.PropositionalEquality public

-- PA primitive recursive functions
_+_ : M → M → M
zero   + n = n
succ m + n = succ (m + n)

_*_ : M → M → M
zero   * n = zero
succ m * n = n + m * n

------------------------------------------------------------------------------
-- ATPs helper
-- We don't traslate the body of functions, only the types. Therefore
-- we need to feed the ATPs with the functions' equations.

-- Addition axioms
+-0x : ∀ n → zero + n ≡ n
+-0x n = refl
-- {-# ATP hint +-0x #-}

+-Sx : ∀ m n → succ m + n ≡ succ (m + n)
+-Sx m n = refl
{-# ATP hint +-Sx #-}

-- Multiplication axioms
*-0x : ∀ n → zero * n ≡ zero
*-0x n = refl
-- {-# ATP hint *-0x #-}

*-Sx : ∀ m n → succ m * n ≡ n + m * n
*-Sx m n = refl
-- {-# ATP hint *-Sx #-}
