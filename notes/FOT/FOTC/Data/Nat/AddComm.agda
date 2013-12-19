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
  is {i} Ai = trans (+-Sx i zero) (succCong Ai)

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

+-comm-ind-instance :
  ∀ n →
  zero + n ≡ n + zero →
  (∀ {m} → m + n ≡ n + m → succ₁ m + n ≡ n + succ₁ m) →
  ∀ {m} → N m → m + n ≡ n + m
+-comm-ind-instance n = N-ind (λ i → i + n ≡ n + i)

------------------------------------------------------------------------------
-- Approach 1: Interactive proof using pattern matching

module M₁ where

  +-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
  +-comm {n = n} nzero Nn =
    zero + n ≡⟨ +-leftIdentity n ⟩
    n        ≡⟨ sym (+-rightIdentity Nn) ⟩
    n + zero ∎

  +-comm {n = n} (nsucc {m} Nm) Nn =
    succ₁ m + n   ≡⟨ +-Sx m n ⟩
    succ₁ (m + n) ≡⟨ succCong (+-comm Nm Nn) ⟩
    succ₁ (n + m) ≡⟨ sym (x+Sy≡S[x+y] Nn m) ⟩
    n + succ₁ m   ∎

------------------------------------------------------------------------------
-- Approach 2: Combined proof using pattern matching

module M₂ where

  +-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
  +-comm {n = n} nzero Nn = prf
    where postulate prf : zero + n ≡ n + zero
          {-# ATP prove prf +-rightIdentity #-}
  +-comm {n = n} (nsucc {m} Nm) Nn = prf (+-comm Nm Nn)
    where postulate prf : m + n ≡ n + m → succ₁ m + n ≡ n + succ₁ m
          {-# ATP prove prf x+Sy≡S[x+y] #-}

------------------------------------------------------------------------------
-- Approach 3: Interactive proof using the induction principle

module M₃ where

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

------------------------------------------------------------------------------
-- Approach 4: Combined proof using the induction principle

module M₄ where

  +-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
  +-comm {n = n} Nm Nn = N-ind A A0 is Nm
    where
    A : D → Set
    A i = i + n ≡ n + i
    {-# ATP definition A #-}

    postulate A0 : A zero
    {-# ATP prove A0 +-rightIdentity #-}

    postulate is : ∀ {i} → A i → A (succ₁ i)
    {-# ATP prove is x+Sy≡S[x+y] #-}

------------------------------------------------------------------------------
-- Approach 5: Interactive proof using an instance of the induction
-- principle

module M₅ where

  +-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
  +-comm {n = n} Nm Nn = +-comm-ind-instance n A0 is Nm
    where
    A0 : zero + n ≡ n + zero
    A0 = zero + n ≡⟨ +-leftIdentity n ⟩
         n        ≡⟨ sym (+-rightIdentity Nn) ⟩
         n + zero ∎

    is : ∀ {i} → i + n ≡ n + i → succ₁ i + n ≡ n + succ₁ i
    is {i} ih = succ₁ i + n   ≡⟨ +-Sx i n ⟩
                succ₁ (i + n) ≡⟨ succCong ih ⟩
                succ₁ (n + i) ≡⟨ sym (x+Sy≡S[x+y] Nn i) ⟩
                n + succ₁ i   ∎

------------------------------------------------------------------------------
-- Approach 6: Combined proof using an instance of the induction
-- principle

module M₆ where

  -- TODO (25 October 2012): Why is it not necessary the hypothesis
  -- +-rightIdentity?
  postulate +-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
  {-# ATP prove +-comm +-comm-ind-instance x+Sy≡S[x+y] #-}
