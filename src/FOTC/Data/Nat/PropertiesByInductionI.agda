------------------------------------------------------------------------------
-- Arithmetic properties (using induction on the FOTC natural numbers type)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Usually our proofs use pattern matching instead of the induction
-- principle associated with the FOTC natural numbers. The following
-- examples show some proofs using it.

module FOTC.Data.Nat.PropertiesByInductionI where

open import Common.Function

open import FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.Nat

------------------------------------------------------------------------------

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = +-0x n

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity Nn = N-ind P P0 is Nn
  where
  P : D → Set
  P i = i + zero ≡ i

  P0 : P zero
  P0 = +-leftIdentity zero

  is : ∀ {i} → P i → P (succ₁ i)
  is {i} Pi = trans (+-Sx i zero)
                    (subst (λ t → succ₁ (i + zero) ≡ succ₁ t)
                           Pi
                             refl
                    )

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} Nm Nn = N-ind P P0 is Nm
  where
  P : D → Set
  P i = N (i + n)

  P0 : P zero
  P0 = subst N (sym $ +-leftIdentity n) Nn

  is : ∀ {i} → P i → P (succ₁ i)
  is {i} Pi = subst N (sym $ +-Sx i n) (sN Pi)

+-assoc : ∀ {m n o} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} Nm Nn No = N-ind P P0 is Nm
  where
  P : D → Set
  P i = i + n + o ≡ i + (n + o)

  P0 : P zero
  P0 =
     zero + n + o
       ≡⟨ subst (λ t → zero + n + o ≡ t + o) (+-leftIdentity n) refl ⟩
     n + o
       ≡⟨ sym $ +-leftIdentity (n + o) ⟩
     zero + (n + o) ∎

  is : ∀ {i} → P i → P (succ₁ i)
  is {i} Pi =
    succ₁ i + n + o
      ≡⟨ subst (λ t → succ₁ i + n + o ≡ t + o) (+-Sx i n) refl ⟩
    succ₁ (i + n) + o
      ≡⟨ +-Sx (i + n) o ⟩
    succ₁ (i + n + o)
      ≡⟨ subst (λ t → succ₁ (i + n + o) ≡ succ₁ t) Pi refl ⟩
    succ₁ (i + (n + o))
      ≡⟨ sym $ +-Sx i (n + o) ⟩
    succ₁ i + (n + o) ∎

x+Sy≡S[x+y] : ∀ {m} n → N m → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y] n Nm = N-ind P P0 is Nm
  where
  P : D → Set
  P i = i + succ₁ n ≡ succ₁ (i + n)

  P0 : P zero
  P0 =
    zero + succ₁ n
      ≡⟨ +-0x (succ₁ n) ⟩
    succ₁ n
      ≡⟨ subst (λ t → succ₁ n ≡ succ₁ t) (sym $ +-leftIdentity n) refl ⟩
    succ₁ (zero + n) ∎

  is : ∀ {i} → P i → P (succ₁ i)
  is {i} Pi =
    succ₁ i + succ₁ n
      ≡⟨ +-Sx i (succ₁ n) ⟩
    succ₁ (i + succ₁ n)
      ≡⟨ subst (λ t → succ₁ (i + succ₁ n) ≡ succ₁ t) Pi refl ⟩
    succ₁ (succ₁ (i + n))
      ≡⟨ subst (λ t → succ₁ (succ₁ (i + n)) ≡ succ₁ t) (sym $ +-Sx i n) refl ⟩
    succ₁ (succ₁ i + n) ∎

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} Nm Nn = N-ind P P0 is Nm
  where
  P : D → Set
  P i = i + n ≡ n + i

  P0 : P zero
  P0 =
    zero + n ≡⟨ +-leftIdentity n ⟩
    n        ≡⟨ sym $ +-rightIdentity Nn ⟩
    n + zero ∎

  is : ∀ {i} → P i → P (succ₁ i)
  is {i} Pi =
     succ₁ i + n
       ≡⟨ +-Sx i n ⟩
     succ₁ (i + n)
        ≡⟨ subst (λ t → succ₁ (i + n) ≡ succ₁ t) Pi refl ⟩
     succ₁ (n + i)
       ≡⟨ sym $ x+Sy≡S[x+y] i Nn ⟩
     n + succ₁ i ∎
