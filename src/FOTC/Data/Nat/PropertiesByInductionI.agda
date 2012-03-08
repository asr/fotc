------------------------------------------------------------------------------
-- Arithmetic properties (using induction on the FOTC natural numbers type)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Usually our proofs use pattern matching instead of the induction
-- principle associated with the FOTC natural numbers. The following
-- examples show some proofs using it.

module FOTC.Data.Nat.PropertiesByInductionI where

open import Common.FOL.Relation.Binary.EqReasoning
open import Common.Function

open import FOTC.Base
open import FOTC.Data.Nat

------------------------------------------------------------------------------

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = +-0x n

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity Nn = N-ind A A0 is Nn
  where
  A : D → Set
  A i = i + zero ≡ i

  A0 : A zero
  A0 = +-leftIdentity zero

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} ih = trans (+-Sx i zero)
                    (subst (λ t → succ₁ (i + zero) ≡ succ₁ t)
                           ih
                           refl
                    )

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} Nm Nn = N-ind A A0 is Nm
  where
  A : D → Set
  A i = N (i + n)

  A0 : A zero
  A0 = subst N (sym $ +-leftIdentity n) Nn

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} ih = subst N (sym $ +-Sx i n) (sN ih)

+-assoc : ∀ {m n o} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} Nm Nn No = N-ind A A0 is Nm
  where
  A : D → Set
  A i = i + n + o ≡ i + (n + o)

  A0 : A zero
  A0 =
     zero + n + o
       ≡⟨ subst (λ t → zero + n + o ≡ t + o) (+-leftIdentity n) refl ⟩
     n + o
       ≡⟨ sym $ +-leftIdentity (n + o) ⟩
     zero + (n + o) ∎

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} ih =
    succ₁ i + n + o
      ≡⟨ subst (λ t → succ₁ i + n + o ≡ t + o) (+-Sx i n) refl ⟩
    succ₁ (i + n) + o
      ≡⟨ +-Sx (i + n) o ⟩
    succ₁ (i + n + o)
      ≡⟨ subst (λ t → succ₁ (i + n + o) ≡ succ₁ t) ih refl ⟩
    succ₁ (i + (n + o))
      ≡⟨ sym $ +-Sx i (n + o) ⟩
    succ₁ i + (n + o) ∎

x+Sy≡S[x+y] : ∀ {m} n → N m → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y] n Nm = N-ind A A0 is Nm
  where
  A : D → Set
  A i = i + succ₁ n ≡ succ₁ (i + n)

  A0 : A zero
  A0 =
    zero + succ₁ n
      ≡⟨ +-0x (succ₁ n) ⟩
    succ₁ n
      ≡⟨ subst (λ t → succ₁ n ≡ succ₁ t) (sym $ +-leftIdentity n) refl ⟩
    succ₁ (zero + n) ∎

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} ih =
    succ₁ i + succ₁ n
      ≡⟨ +-Sx i (succ₁ n) ⟩
    succ₁ (i + succ₁ n)
      ≡⟨ subst (λ t → succ₁ (i + succ₁ n) ≡ succ₁ t) ih refl ⟩
    succ₁ (succ₁ (i + n))
      ≡⟨ subst (λ t → succ₁ (succ₁ (i + n)) ≡ succ₁ t) (sym $ +-Sx i n) refl ⟩
    succ₁ (succ₁ i + n) ∎

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} Nm Nn = N-ind A A0 is Nm
  where
  A : D → Set
  A i = i + n ≡ n + i

  A0 : A zero
  A0 =
    zero + n ≡⟨ +-leftIdentity n ⟩
    n        ≡⟨ sym $ +-rightIdentity Nn ⟩
    n + zero ∎

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} ih =
     succ₁ i + n
       ≡⟨ +-Sx i n ⟩
     succ₁ (i + n)
        ≡⟨ cong succ₁ ih ⟩
     succ₁ (n + i)
       ≡⟨ sym $ x+Sy≡S[x+y] i Nn ⟩
     n + succ₁ i ∎
