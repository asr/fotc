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

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Nat
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- Congruence properties

+-leftCong : ∀ {a b c} → a ≡ b → a + c ≡ b + c
+-leftCong refl = refl

+-rightCong : ∀ {a b c} → b ≡ c → a + b ≡ a + c
+-rightCong refl = refl

------------------------------------------------------------------------------

N→0∨S : ∀ {n} → N n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n')
N→0∨S = N-ind A A0 is
  where
  A : D → Set
  A i = i ≡ zero ∨ (∃[ i' ] i ≡ succ₁ i' ∧ N i')

  A0 : A zero
  A0 = inj₁ refl

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} Ai = case prf₁ prf₂ Ai
    where
    prf₁ : i ≡ zero → succ₁ i ≡ zero ∨ (∃[ i' ] succ₁ i ≡ succ₁ i' ∧ N i')
    prf₁ h' = inj₂ (i , refl , (subst N (sym h') nzero))

    prf₂ : ∃[ i' ] i ≡ succ₁ i' ∧ N i' →
           succ₁ i ≡ zero ∨ (∃[ i' ] succ₁ i ≡ succ₁ i' ∧ N i')
    prf₂ (i' , prf , Ni') = inj₂ (i , refl , subst N (sym prf) (nsucc Ni'))

Sx≢x : ∀ {n} → N n → succ₁ n ≢ n
Sx≢x = N-ind A A0 is
  where
  A : D → Set
  A i = succ₁ i ≢ i

  A0 : A zero
  A0 = S≢0

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} Ai = →-trans succInjective Ai

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = +-0x n

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity = N-ind A A0 is
  where
  A : D → Set
  A i = i + zero ≡ i

  A0 : A zero
  A0 = +-leftIdentity zero

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} Ai = trans (+-Sx i zero) (succCong Ai)

pred-N : ∀ {n} → N n → N (pred₁ n)
pred-N {n} Nn = case h₁ h₂ (N→0∨S Nn)
  where
  h₁ : n ≡ zero → N (pred₁ n)
  h₁ n≡0 = subst N (sym (trans (predCong n≡0) pred-0)) nzero

  h₂ : ∃[ n' ] n ≡ succ₁ n' ∧ N n' → N (pred₁ n)
  h₂ (n' , prf , Nn') = subst N (sym (trans (predCong prf) (pred-S n'))) Nn'

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} Nm Nn = N-ind A A0 is Nm
  where
  A : D → Set
  A i = N (i + n)

  A0 : A zero
  A0 = subst N (sym (+-leftIdentity n)) Nn

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} Ai = subst N (sym (+-Sx i n)) (nsucc Ai)

+-assoc : ∀ {m} → N m → ∀ n o → m + n + o ≡ m + (n + o)
+-assoc Nm n o = N-ind A A0 is Nm
  where
  A : D → Set
  A i = i + n + o ≡ i + (n + o)

  A0 : A zero
  A0 = zero + n + o   ≡⟨ +-leftCong (+-leftIdentity n) ⟩
       n + o          ≡⟨ sym (+-leftIdentity (n + o)) ⟩
       zero + (n + o) ∎

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} Ai = succ₁ i + n + o     ≡⟨ +-leftCong (+-Sx i n) ⟩
              succ₁ (i + n) + o   ≡⟨ +-Sx (i + n) o ⟩
              succ₁ (i + n + o)   ≡⟨ succCong Ai ⟩
              succ₁ (i + (n + o)) ≡⟨ sym (+-Sx i (n + o)) ⟩
              succ₁ i + (n + o)   ∎

x+Sy≡S[x+y] : ∀ {m} → N m → ∀ n → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y] Nm n = N-ind A A0 is Nm
  where
  A : D → Set
  A i = i + succ₁ n ≡ succ₁ (i + n)

  A0 : A zero
  A0 = zero + succ₁ n   ≡⟨ +-leftIdentity (succ₁ n) ⟩
       succ₁ n          ≡⟨ succCong (sym (+-leftIdentity n)) ⟩
       succ₁ (zero + n) ∎

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} Ai = succ₁ i + succ₁ n     ≡⟨ +-Sx i (succ₁ n) ⟩
              succ₁ (i + succ₁ n)   ≡⟨ succCong Ai ⟩
              succ₁ (succ₁ (i + n)) ≡⟨ succCong (sym (+-Sx i n)) ⟩
              succ₁ (succ₁ i + n)   ∎

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} Nm Nn = N-ind A A0 is Nm
  where
  A : D → Set
  A i = i + n ≡ n + i

  A0 : A zero
  A0 = zero + n ≡⟨ +-leftIdentity n ⟩
       n        ≡⟨ sym (+-rightIdentity Nn) ⟩
       n + zero ∎

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} Ai = succ₁ i + n   ≡⟨ +-Sx i n ⟩
              succ₁ (i + n) ≡⟨ succCong Ai ⟩
              succ₁ (n + i) ≡⟨ sym (x+Sy≡S[x+y] Nn i) ⟩
              n + succ₁ i   ∎

0∸x : ∀ {n} → N n → zero ∸ n ≡ zero
0∸x = N-ind A A0 is
  where
  A : D → Set
  A i = zero ∸ i ≡ zero

  A0 : A zero
  A0 = ∸-x0 zero

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} Ai = zero ∸ succ₁ i   ≡⟨ ∸-xS zero i ⟩
              pred₁ (zero ∸ i) ≡⟨ predCong Ai ⟩
              pred₁ zero       ≡⟨ pred-0 ⟩
              zero ∎
