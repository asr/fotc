------------------------------------------------------------------------------
-- Arithmetic properties using instances of the induction principle
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.Induction.AdditionalHypothesis.Instances.PropertiesATP
  where

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

-- The ATPs could not prove this conjecture.
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

------------------------------------------------------------------------------
-- From now on we will use the N-ind₁ induction principle.

N-ind = N-ind₁

∸-N-ind-instance :
  ∀ {m} →
  N (m ∸ zero) →
  (∀ {n} → N n → N (m ∸ n) → N (m ∸ succ₁ n)) →
  ∀ {n} → N n → N (m ∸ n)
∸-N-ind-instance {n} = N-ind (λ i → N (n ∸ i))

postulate ∸-N : ∀ {m n} → N m → N n → N (m ∸ n)
{-# ATP prove ∸-N ∸-N-ind-instance pred-N₁ #-}

*-N-ind-instance :
  ∀ {n} →
  N (zero * n) →
  (∀ {m} → N m → N (m * n) → N (succ₁ m * n)) →
  ∀ {m} → N m → N (m * n)
*-N-ind-instance {n} = N-ind (λ i → N (i * n))

postulate *-N : ∀ {m n} → N m → N n → N (m * n)
{-# ATP prove *-N *-N-ind-instance +-N₁ #-}

+-rightIdentity-ind-instance :
  zero + zero ≡ zero →
  (∀ {n} → N n → n + zero ≡ n → succ₁ n + zero ≡ succ₁ n) →
  ∀ {n} → N n → n + zero ≡ n
+-rightIdentity-ind-instance = N-ind (λ i → i + zero ≡ i)

postulate +-rightIdentity : ∀ {n} → N n → n + zero ≡ n
{-# ATP prove +-rightIdentity +-rightIdentity-ind-instance #-}

+-assoc-ind-instance :
  ∀ {n} {o} →
  zero + n + o ≡ zero + (n + o) →
  (∀ {m} → N m →
    m + n + o ≡ m + (n + o) → succ₁ m + n + o ≡ succ₁ m + (n + o)) →
  ∀ {m} → N m → m + n + o ≡ m + (n + o)
+-assoc-ind-instance {n} {o} = N-ind (λ i → i + n + o ≡ i + (n + o))

postulate +-assoc : ∀ {m} → N m → ∀ n o → m + n + o ≡ m + (n + o)
{-# ATP prove +-assoc +-assoc-ind-instance #-}

x+Sy≡S[x+y]-ind-instance :
  ∀ {n} →
  zero + succ₁ n ≡ succ₁ (zero + n) →
  (∀ {m} → N m →
    m + succ₁ n ≡ succ₁ (m + n) → succ₁ m + succ₁ n ≡ succ₁ (succ₁ m + n)) →
  ∀ {m} → N m → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y]-ind-instance {n} = N-ind (λ i → i + succ₁ n ≡ succ₁ (i + n))

postulate x+Sy≡S[x+y] : ∀ {m} → N m → ∀ n → m + succ₁ n ≡ succ₁ (m + n)
{-# ATP prove x+Sy≡S[x+y] x+Sy≡S[x+y]-ind-instance #-}

+-comm-ind-instance :
  ∀ {n} →
  zero + n ≡ n + zero →
  (∀ {m} → N m → m + n ≡ n + m → succ₁ m + n ≡ n + succ₁ m) →
  ∀ {m} → N m → m + n ≡ n + m
+-comm-ind-instance {n} = N-ind (λ i → i + n ≡ n + i)

postulate +-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
{-# ATP prove +-comm +-comm-ind-instance +-rightIdentity x+Sy≡S[x+y] #-}
