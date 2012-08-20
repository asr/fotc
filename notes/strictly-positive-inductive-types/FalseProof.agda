{-# OPTIONS --no-positivity-check #-}

-- Using a non-strictly positive type is possible to get a
-- contradiction. From Coq' Art, section 14.1.2.1.

module FalseProof where

open import Data.Nat
open import Relation.Binary.PropositionalEquality
-- open ≡-Reasoning
open import Relation.Nullary

n≠Sn : ∀ n → ¬ (n ≡ suc n)
n≠Sn n ()

data T : Set where
  l : (T → T) → T

depth : T → ℕ
depth (l f) = suc (depth (f (l f)))

-- Then:
--
-- depth (l (λ t → t)) =
-- suc (depth ((λ t → t) (l (λ t → t)))) =
-- suc (depth (l (λ t → t)))

-- which contradicts the theorem n≠Sn.
