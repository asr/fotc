------------------------------------------------------------------------------
-- Arithmetic properties (using induction on the LTC natural numbers type)
------------------------------------------------------------------------------

-- Usually our proofs use pattern matching instead of the induction
-- principle associated with the LTC natural numbers. The following
-- examples show some proofs using it.

module LTC.Data.Nat.PropertiesByInductionI where

open import LTC.Base

open import Common.Function

open import LTC.Data.Nat

open import LTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

+-leftIdentity : ∀ {n} → N n → zero + n ≡ n
+-leftIdentity {n} _ = +-0x n

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity Nn = indN P P0 iStep Nn
  where
    P : D → Set
    P i = i + zero ≡ i

    P0 : P zero
    P0 = +-leftIdentity zN

    iStep : ∀ {i} → N i → P i → P (succ i)
    iStep {i} Ni Pi =
        trans (+-Sx i zero)
              (subst (λ t → succ (i + zero) ≡ succ t)
                     Pi
                     refl
              )

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} Nm Nn = indN P P0 iStep Nm
  where
    P : D → Set
    P i = N (i + n)

    P0 : P zero
    P0 = subst N (sym $ +-leftIdentity Nn) Nn

    iStep : ∀ {i} → N i → P i → P (succ i)
    iStep {i} Ni Pi = subst N (sym $ +-Sx i n) (sN Pi)

+-assoc : ∀ {m n o} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} Nm Nn No = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + n + o ≡ i + (n + o)

    P0 : P zero
    P0 =
      begin
        zero + n + o ≡⟨ subst (λ t → zero + n + o ≡ t + o)
                              (+-leftIdentity Nn)
                              refl
                     ⟩
        n + o        ≡⟨ sym $ +-leftIdentity (+-N Nn No) ⟩
        zero + (n + o)
      ∎

    iStep : ∀ {i} → N i → P i → P (succ i)
    iStep {i} Ni Pi =
      begin
        succ i + n + o     ≡⟨ subst (λ t → succ i + n + o ≡ t + o)
                              (+-Sx i n)
                              refl
                           ⟩
        succ (i + n) + o   ≡⟨ +-Sx (i + n) o ⟩
        succ (i + n + o)   ≡⟨ subst (λ t → succ (i + n + o) ≡ succ t)
                                    Pi
                                    refl
                           ⟩
        succ (i + (n + o)) ≡⟨ sym $ +-Sx i (n + o) ⟩
        succ i + (n + o)
      ∎

x+Sy≡S[x+y] : ∀ {m n} → N m → N n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] {n = n} Nm Nn = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + succ n ≡ succ (i + n)

    P0 : P zero
    P0 =
      begin
        zero + succ n ≡⟨ +-0x (succ n) ⟩
        succ n        ≡⟨ subst (λ t → succ n ≡ succ t)
                               (sym $ +-leftIdentity Nn)
                               refl
                      ⟩
        succ (zero + n)
      ∎

    iStep : ∀ {i} → N i → P i → P (succ i)
    iStep {i} Ni Pi =
      begin
        succ i + succ n     ≡⟨ +-Sx i (succ n) ⟩
        succ (i + succ n)   ≡⟨ subst (λ t → succ (i + succ n) ≡ succ t)
                                     Pi
                                     refl
                            ⟩
        succ (succ (i + n)) ≡⟨ subst (λ t → succ (succ (i + n)) ≡ succ t)
                                     (sym $ +-Sx i n)
                                     refl
                            ⟩
        succ (succ i + n)
      ∎

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} Nm Nn = indN P P0 iStep Nm
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

    iStep : ∀ {i} → N i → P i → P (succ i)
    iStep {i} Ni Pi =
      begin
        succ i + n   ≡⟨ +-Sx i n ⟩
        succ (i + n) ≡⟨ subst (λ t → succ (i + n) ≡ succ t)
                              Pi
                              refl
                     ⟩
        succ (n + i) ≡⟨ sym $ x+Sy≡S[x+y] Nn Ni ⟩
        n + succ i
      ∎
