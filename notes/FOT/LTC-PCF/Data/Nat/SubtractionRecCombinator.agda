------------------------------------------------------------------------------
-- Subtraction using the rec combinator
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.LTC-PCF.Data.Nat.SubtractionRecCombinator where

open import Common.FOL.Relation.Binary.EqReasoning

open import LTC-PCF.Base
open import LTC-PCF.Base.Properties
open import LTC-PCF.Data.Nat.Properties hiding ( ∸-x0 ; ∸-0x ; ∸-0S ; ∸-SS )
open import LTC-PCF.Data.Nat.Rec
open import LTC-PCF.Data.Nat.Rec.Equations
open import LTC-PCF.Data.Nat.Type

-- We add 3 to the fixities of the standard library.
infixl 9 _∸_

------------------------------------------------------------------------------

-- Subtraction
_∸_ : D → D → D
m ∸ n = rec n m (lam (λ _ → lam pred₁))

-- Conversion rules (from the Agda standard library)

∸-x0 : ∀ n → n ∸ zero ≡ n
∸-x0 n = rec zero n _ ≡⟨ rec-0 n ⟩
         n            ∎

∸-0S : ∀ {n} → N n → zero ∸ succ₁ n ≡ zero
∸-0S nzero =
  rec (succ₁ zero) zero (lam (λ _ → lam pred₁))
    ≡⟨ rec-S zero zero (lam (λ _ → lam pred₁)) ⟩
  lam (λ _ → lam pred₁) · zero · (zero ∸ zero)
    ≡⟨ ·-leftCong (beta (λ _ → lam pred₁) zero) ⟩
  lam pred₁ · (zero ∸ zero)
    ≡⟨ beta pred₁ (zero ∸ zero) ⟩
  pred₁ (zero ∸ zero)
    ≡⟨ predCong (∸-x0 zero) ⟩
  pred₁ zero
    ≡⟨ pred-0 ⟩
  zero ∎

∸-0S (nsucc {n} Nn) =
  rec (succ₁ (succ₁ n)) zero (lam (λ _ → lam pred₁))
    ≡⟨ rec-S (succ₁ n) zero (lam (λ _ → lam pred₁)) ⟩
  lam (λ _ → lam pred₁) · (succ₁ n) · (zero ∸ (succ₁ n))
    ≡⟨ ·-leftCong (beta (λ _ → lam pred₁) (succ₁ n)) ⟩
  lam pred₁ · (zero ∸ (succ₁ n))
    ≡⟨ beta pred₁ (zero ∸ (succ₁ n)) ⟩
  pred₁ (zero ∸ (succ₁ n))
    ≡⟨ predCong (∸-0S Nn) ⟩
  pred₁ zero
    ≡⟨ pred-0 ⟩
  zero ∎

∸-0x : ∀ {n} → N n → zero ∸ n ≡ zero
∸-0x nzero      = ∸-x0 zero
∸-0x (nsucc Nn) = ∸-0S Nn

∸-SS : ∀ {m n} → N m → N n → succ₁ m ∸ succ₁ n ≡ m ∸ n
∸-SS {m} _ nzero =
  rec (succ₁ zero) (succ₁ m) (lam (λ _ → lam pred₁))
    ≡⟨ rec-S zero (succ₁ m) (lam (λ _ → lam pred₁)) ⟩
  lam (λ _ → lam pred₁) · zero · (succ₁ m ∸ zero)
    ≡⟨ ·-leftCong (beta (λ _ → lam pred₁) zero) ⟩
  lam pred₁ · (succ₁ m ∸ zero)
    ≡⟨ beta pred₁ (succ₁ m ∸ zero) ⟩
  pred₁ (succ₁ m ∸ zero)
    ≡⟨ predCong (∸-x0 (succ₁ m)) ⟩
  pred₁ (succ₁ m)
    ≡⟨ pred-S m ⟩
  m
    ≡⟨ sym (∸-x0 m) ⟩
  m ∸ zero ∎

∸-SS nzero (nsucc {n} Nn) =
  rec (succ₁ (succ₁ n)) (succ₁ zero) (lam (λ _ → lam pred₁))
    ≡⟨ rec-S (succ₁ n) (succ₁ zero) (lam (λ _ → lam pred₁))  ⟩
  lam (λ _ → lam pred₁) · (succ₁ n) · (succ₁ zero ∸ succ₁ n)
    ≡⟨ ·-leftCong (beta (λ _ → lam pred₁) (succ₁ n)) ⟩
  lam pred₁ · (succ₁ zero ∸ succ₁ n)
    ≡⟨ beta pred₁ (succ₁ zero ∸ succ₁ n) ⟩
  pred₁ (succ₁ zero ∸ succ₁ n)
    ≡⟨ predCong (∸-SS nzero Nn) ⟩
  pred₁ (zero ∸ n)
    ≡⟨ predCong (∸-0x Nn) ⟩
  pred₁ zero
    ≡⟨ pred-0 ⟩
  zero
    ≡⟨ sym (∸-0S Nn) ⟩
  zero ∸ succ₁ n ∎

∸-SS (nsucc {m} Nm) (nsucc {n} Nn) =
  rec (succ₁ (succ₁ n)) (succ₁ (succ₁ m)) (lam (λ _ → lam pred₁))
    ≡⟨ rec-S (succ₁ n) (succ₁ (succ₁ m)) (lam (λ _ → lam pred₁)) ⟩
  lam (λ _ → lam pred₁) · (succ₁ n) · (succ₁ (succ₁ m) ∸ succ₁ n)
    ≡⟨ ·-leftCong (beta (λ _ → lam pred₁) (succ₁ n)) ⟩
  lam pred₁ · (succ₁ (succ₁ m) ∸ succ₁ n)
    ≡⟨ beta pred₁ (succ₁ (succ₁ m) ∸ succ₁ n) ⟩
  pred₁ (succ₁ (succ₁ m) ∸ succ₁ n)
    ≡⟨ predCong (∸-SS (nsucc Nm) Nn) ⟩
  pred₁ (succ₁ m ∸ n)
    ≡⟨ sym (beta pred₁ (succ₁ m ∸ n)) ⟩
  lam pred₁ · (succ₁ m ∸ n)
    ≡⟨ ·-leftCong (sym (beta (λ _ → lam pred₁) n)) ⟩
  (lam (λ _ → lam pred₁)) · n · (succ₁ m ∸ n)
    ≡⟨ sym (rec-S n (succ₁ m) (lam (λ _ → lam pred₁))) ⟩
  rec (succ₁ n) (succ₁ m) (lam (λ _ → lam pred₁))
    ≡⟨ refl ⟩
  succ₁ m ∸ succ₁ n ∎

------------------------------------------------------------------------------
-- Conversion rules from the Agda standard library without totality
-- hypotheses.

-- We could not prove this property.
-- ∸-0S₁ : ∀ n → zero ∸ succ₁ n ≡ zero
-- ∸-0S₁ n =
--   rec (succ₁ n) zero (lam (λ _ → lam pred₁))
--     ≡⟨ rec-S n zero (lam (λ _ → lam pred₁)) ⟩
--   lam (λ _ → lam pred₁) · n · (zero ∸ n)
--     ≡⟨ ·-leftCong (beta (λ _ → lam pred₁) n) ⟩
--   lam pred₁ · (zero ∸ n)
--     ≡⟨ beta pred₁ (zero ∸ n) ⟩
--   pred₁ (zero ∸ n)
--     ≡⟨ {!!} ⟩
--   {!!}
--     ≡⟨ {!!} ⟩
--   zero ∎

-- We could not prove this property.
-- ∸-SS₁ : ∀ m n → succ₁ m ∸ succ₁ n ≡ m ∸ n
-- ∸-SS₁ m n =
--   rec (succ₁ n) (succ₁ m) (lam (λ _ → lam pred₁))
--   ≡⟨ rec-S n (succ₁ m) (lam (λ _ → lam pred₁)) ⟩
--   lam (λ x → lam pred₁) · n · (succ₁ m ∸ n)
--     ≡⟨ ·-leftCong (beta (λ _ → lam pred₁) n) ⟩
--   lam pred₁ · (succ₁ m ∸ n)
--     ≡⟨ beta pred₁ (succ₁ m ∸ n) ⟩
--   pred₁ (succ₁ m ∸ n)
--     ≡⟨ {!!} ⟩
--   {!!}
--     ≡⟨ {!!} ⟩
--   m ∸ n ∎

------------------------------------------------------------------------------
-- Coq conversion rules

-- Fixpoint minus (n m:nat) : nat :=
--   match n, m with
--   | O, _ => n
--   | S k, O => S k
--   | S k, S l => k - l
--   end

∸-x0-coq : ∀ n → n ∸ zero ≡ n
∸-x0-coq n = rec zero n _ ≡⟨ rec-0 n ⟩
             n            ∎

∸-S0-coq : ∀ n → succ₁ n ∸ zero ≡ succ₁ n
∸-S0-coq n =
  rec zero (succ₁ n) (lam (λ _ → lam pred₁))
    ≡⟨ rec-0 (succ₁ n) ⟩
  succ₁ n ∎

-- We could not prove this property.
-- ∸-SS-coq : ∀ m n → succ₁ m ∸ succ₁ n ≡ m ∸ n
-- ∸-SS-coq m n =
--   rec (succ₁ n) (succ₁ m) (lam (λ _ → lam pred₁))
--   ≡⟨ rec-S n (succ₁ m) (lam (λ _ → lam pred₁)) ⟩
--   lam (λ x → lam pred₁) · n · (succ₁ m ∸ n)
--     ≡⟨ ·-leftCong (beta (λ _ → lam pred₁) n) ⟩
--   lam pred₁ · (succ₁ m ∸ n)
--     ≡⟨ beta pred₁ (succ₁ m ∸ n) ⟩
--   pred₁ (succ₁ m ∸ n)
--     ≡⟨ {!!} ⟩
--   {!!}
--     ≡⟨ {!!} ⟩
--   m ∸ n ∎
