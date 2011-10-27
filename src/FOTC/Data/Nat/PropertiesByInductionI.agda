------------------------------------------------------------------------------
-- Arithmetic properties (using induction on the FOTC natural numbers type)
------------------------------------------------------------------------------

-- Usually our proofs use pattern matching instead of the induction
-- principle associated with the FOTC natural numbers. The following
-- examples show some proofs using it.

module FOTC.Data.Nat.PropertiesByInductionI where

open import FOTC.Base

open import Common.Function

open import FOTC.Data.Nat

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

+-leftIdentity : ∀ {n} → N n → zero + n ≡ n
+-leftIdentity {n} _ = +-0x n

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity Nn = indN P P0 is Nn
  where
  P : D → Set
  P i = i + zero ≡ i

  P0 : P zero
  P0 = +-leftIdentity zN

  is : ∀ {i} → N i → P i → P (succ₁ i)
  is {i} Ni Pi = trans (+-Sx i zero)
                       (subst (λ t → succ₁ (i + zero) ≡ succ₁ t)
                              Pi
                              refl
                       )

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} Nm Nn = indN P P0 is Nm
  where
  P : D → Set
  P i = N (i + n)

  P0 : P zero
  P0 = subst N (sym $ +-leftIdentity Nn) Nn

  is : ∀ {i} → N i → P i → P (succ₁ i)
  is {i} Ni Pi = subst N (sym $ +-Sx i n) (sN Pi)

+-assoc : ∀ {m n o} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} Nm Nn No = indN P P0 is Nm
  where
  P : D → Set
  P i = i + n + o ≡ i + (n + o)

  P0 : P zero
  P0 =
     begin
       zero + n + o
         ≡⟨ subst (λ t → zero + n + o ≡ t + o)
                  (+-leftIdentity Nn)
                  refl
         ⟩
       n + o ≡⟨ sym $ +-leftIdentity (+-N Nn No) ⟩
       zero + (n + o)
     ∎

  is : ∀ {i} → N i → P i → P (succ₁ i)
  is {i} Ni Pi =
     begin
       succ₁ i + n + o
         ≡⟨ subst (λ t → succ₁ i + n + o ≡ t + o)
                  (+-Sx i n)
                  refl
         ⟩
       succ₁ (i + n) + o ≡⟨ +-Sx (i + n) o ⟩
       succ₁ (i + n + o)
         ≡⟨ subst (λ t → succ₁ (i + n + o) ≡ succ₁ t)
                  Pi
                  refl
         ⟩
       succ₁ (i + (n + o)) ≡⟨ sym $ +-Sx i (n + o) ⟩
       succ₁ i + (n + o)
     ∎

x+Sy≡S[x+y] : ∀ {m n} → N m → N n → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y] {n = n} Nm Nn = indN P P0 is Nm
  where
  P : D → Set
  P i = i + succ₁ n ≡ succ₁ (i + n)

  P0 : P zero
  P0 =
    begin
      zero + succ₁ n ≡⟨ +-0x (succ₁ n) ⟩
      succ₁ n
        ≡⟨ subst (λ t → succ₁ n ≡ succ₁ t)
                 (sym $ +-leftIdentity Nn)
                 refl
                 ⟩
      succ₁ (zero + n)
    ∎

  is : ∀ {i} → N i → P i → P (succ₁ i)
  is {i} Ni Pi =
    begin
      succ₁ i + succ₁ n ≡⟨ +-Sx i (succ₁ n) ⟩
      succ₁ (i + succ₁ n)
        ≡⟨ subst (λ t → succ₁ (i + succ₁ n) ≡ succ₁ t)
                 Pi
                 refl
        ⟩
      succ₁ (succ₁ (i + n))
        ≡⟨ subst (λ t → succ₁ (succ₁ (i + n)) ≡ succ₁ t)
                 (sym $ +-Sx i n)
                 refl
        ⟩
      succ₁ (succ₁ i + n)
    ∎

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} Nm Nn = indN P P0 is Nm
  where
  P : D → Set
  P i = i + n ≡ n + i

  P0 : P zero
  P0 =
    begin
      zero + n ≡⟨ +-leftIdentity Nn ⟩
      n        ≡⟨ sym $ +-rightIdentity Nn ⟩
      n + zero
    ∎

  is : ∀ {i} → N i → P i → P (succ₁ i)
  is {i} Ni Pi =
    begin
      succ₁ i + n ≡⟨ +-Sx i n ⟩
      succ₁ (i + n)
        ≡⟨ subst (λ t → succ₁ (i + n) ≡ succ₁ t)
                 Pi
                 refl
        ⟩
      succ₁ (n + i) ≡⟨ sym $ x+Sy≡S[x+y] Nn Ni ⟩
      n + succ₁ i
    ∎
