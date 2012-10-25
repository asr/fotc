------------------------------------------------------------------------------
-- Commutativity of addition of total natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.AddComm where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.Nat

------------------------------------------------------------------------------
-- Auxiliary properties

succCong : ∀ {m n} → m ≡ n → succ₁ m ≡ succ₁ n
succCong refl = refl

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
  is {i} ih = trans (+-Sx i zero) (succCong ih)

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
  is {i} ih = succ₁ i + succ₁ n     ≡⟨ +-Sx i (succ₁ n) ⟩
              succ₁ (i + succ₁ n)   ≡⟨ succCong ih ⟩
              succ₁ (succ₁ (i + n)) ≡⟨ succCong (sym (+-Sx i n)) ⟩
              succ₁ (succ₁ i + n)   ∎

------------------------------------------------------------------------------
-- Interactive proof using the induction principle for natural numbers.

+-comm₁ : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm₁ {n = n} Nm Nn = N-ind A A0 is Nm
  where
  A : D → Set
  A i = i + n ≡ n + i

  A0 : A zero
  A0 = zero + n ≡⟨ +-leftIdentity n ⟩
       n        ≡⟨ sym (+-rightIdentity Nn) ⟩
       n + zero ∎

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} ih = succ₁ i + n
                ≡⟨ +-Sx i n ⟩
              succ₁ (i + n)
                ≡⟨ succCong ih ⟩
              succ₁ (n + i)
                ≡⟨ sym (x+Sy≡S[x+y] Nn i) ⟩
              n + succ₁ i ∎

------------------------------------------------------------------------------
-- Combined proof

+-comm₂ : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm₂ {n = n} Nm Nn = N-ind A A0 is Nm
  where
  A : D → Set
  A i = i + n ≡ n + i
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 +-rightIdentity #-}

  postulate is : ∀ {i} → A i → A (succ₁ i)
  {-# ATP prove is x+Sy≡S[x+y] #-}

------------------------------------------------------------------------------
-- Combined proof instantiating the induction principle

+-comm-ind : ∀ n →
             (zero + n ≡ n + zero) →
             (∀ {m} → m + n ≡ n + m  → succ₁ m + n ≡ n + succ₁ m) →
             ∀ {m} → N m → m + n ≡ n + m
+-comm-ind n = N-ind (λ i → i + n ≡ n + i)

-- TODO. 25 October 2012. Why is it not necessary the hypothesis
-- +-rightIdentity ?
postulate +-comm₃ : ∀ {m n} → N m → N n → m + n ≡ n + m
{-# ATP prove +-comm₃ +-comm-ind x+Sy≡S[x+y] #-}
