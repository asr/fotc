------------------------------------------------------------------------------
-- Discussion about the inductive approach
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Andrés: From our discussion about the inductive approach, can I
-- conclude that it is possible to rewrite the proofs using pattern
-- matching on _≡_, by proofs using only subst, because the types
-- associated with these proofs haven't proof terms?

-- Peter: Yes, provided the RHS of the definition does not refer to the
-- function defined, i e, there is no recursion.

module FOT.FOTC.InductiveApproach.Recursion where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Nat
open import FOTC.Data.Nat.PropertiesI

------------------------------------------------------------------------------

-- foo is recursive and we pattern matching on _≡_.
foo : ∀ {m n} → N m → m ≡ n → N (m + n)
foo nzero refl = subst N (sym (+-leftIdentity zero)) nzero
foo (nsucc {m} Nm) refl = subst N helper (nsucc (nsucc (foo Nm refl)))
  where
  helper : succ₁ (succ₁ (m + m)) ≡ succ₁ m + succ₁ m
  helper =
    succ₁ (succ₁ (m + m)) ≡⟨ succCong (sym (+-Sx m m))  ⟩
    succ₁ (succ₁ m + m)   ≡⟨ succCong (+-comm (nsucc Nm) Nm) ⟩
    succ₁ (m + succ₁ m)   ≡⟨ sym (+-Sx m (succ₁ m)) ⟩
    succ₁ m + succ₁ m     ∎

-- foo' is recursive and we only use subst.
foo' : ∀ {m n} → N m → m ≡ n → N (m + n)
foo' {n = n} nzero h = subst N (sym (+-leftIdentity n)) (subst N h nzero)
foo' {n = n} (nsucc {m} Nm) h = subst N helper (nsucc (nsucc (foo' Nm refl)))
  where
  helper : succ₁ (succ₁ (m + m)) ≡ succ₁ m + n
  helper =
    succ₁ (succ₁ (m + m)) ≡⟨ succCong (sym (+-Sx m m))  ⟩
    succ₁ (succ₁ m + m)   ≡⟨ succCong (+-comm (nsucc Nm) Nm) ⟩
    succ₁ (m + succ₁ m)   ≡⟨ sym (+-Sx m (succ₁ m)) ⟩
    succ₁ m + succ₁ m     ≡⟨ +-rightCong h ⟩
    succ₁ m + n           ∎
