------------------------------------------------------------------------------
-- Arithmetic properties using instances of the induction principle
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.Induction.Instances.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat hiding ( N-ind )

------------------------------------------------------------------------------
-- Induction principle with the additional hypothesis.
N-ind₁ : (A : D → Set) →
         A zero →
         (∀ {n} → N n → A n → A (succ₁ n)) →
         ∀ {n} → N n → A n
N-ind₁ A A0 h nzero      = A0
N-ind₁ A A0 h (nsucc Nn) = h Nn (N-ind₁ A A0 h Nn)

-- Induction principle without the additional hypothesis.
N-ind₂ : (A : D → Set) →
        A zero →
        (∀ {n} → A n → A (succ₁ n)) →
        ∀ {n} → N n → A n
N-ind₂ A A0 h nzero      = A0
N-ind₂ A A0 h (nsucc Nn) = h (N-ind₂ A A0 h Nn)

------------------------------------------------------------------------------
-- Totality properties

pred-N-ind-instance₁ :
  N (pred₁ zero) →
  (∀ {n} → N n → N (pred₁ n) → N (pred₁ (succ₁ n))) →
  ∀ {n} → N n → N (pred₁ n)
pred-N-ind-instance₁ = N-ind₁ (λ i → N (pred₁ i))

postulate pred-N₁ : ∀ {n} → N n → N (pred₁ n)
{-# ATP prove pred-N₁ pred-N-ind-instance₁ #-}

pred-N-ind-instance₂ :
  N (pred₁ zero) →
  (∀ {n} → N (pred₁ n) → N (pred₁ (succ₁ n))) →
  ∀ {n} → N n → N (pred₁ n)
pred-N-ind-instance₂ = N-ind₂ (λ i → N (pred₁ i))

-- The ATPs could not prove this conjecture
postulate pred-N₂ : ∀ {n} → N n → N (pred₁ n)
-- {-# ATP prove pred-N₂ pred-N-ind-instance₂ #-}

+-N-ind-instance₁ :
  ∀ {n} →
  N (zero + n) →
  (∀ {m} → N m → N (m + n) → N (succ₁ m + n)) →
  ∀ {m} → N m → N (m + n)
+-N-ind-instance₁ {n} = N-ind₁ (λ i → N (i + n))

postulate +-N₁ : ∀ {m n} → N m → N n → N (m + n)
{-# ATP prove +-N₁ +-N-ind-instance₁ #-}

+-N-ind-instance₂ :
  ∀ {n} →
  N (zero + n) →
  (∀ {m} → N (m + n) → N (succ₁ m + n)) →
  ∀ {m} → N m → N (m + n)
+-N-ind-instance₂ {n} = N-ind₂ (λ i → N (i + n))

postulate +-N₂ : ∀ {m n} → N m → N n → N (m + n)
{-# ATP prove +-N₂ +-N-ind-instance₂ #-}
