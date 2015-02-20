------------------------------------------------------------------------------
-- Arithmetic properties using instances of the induction principle
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Data.Nat.Induction.Instances.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat

------------------------------------------------------------------------------
-- Totality properties

N→0∨S-ind-instance :
  zero ≡ zero ∨ (∃[ n' ] zero ≡ succ₁ n' ∧ N n') →
  (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n') →
    succ₁ n ≡ zero ∨ (∃[ n' ] succ₁ n ≡ succ₁ n' ∧ N n')) →
  ∀ {n} → N n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n')
N→0∨S-ind-instance = N-ind (λ i → i ≡ zero ∨ (∃[ i' ] i ≡ succ₁ i' ∧ N i'))

postulate N→0∨S : ∀ {n} → N n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ N n')
{-# ATP prove N→0∨S N→0∨S-ind-instance #-}

pred-N-ind-instance :
  N (pred₁ zero) →
  (∀ {n} → N (pred₁ n) → N (pred₁ (succ₁ n))) →
  ∀ {n} → N n → N (pred₁ n)
pred-N-ind-instance = N-ind (λ i → N (pred₁ i))

-- 09 December 2014. The ATPs could not prove this conjecture.
-- postulate pred-N : ∀ {n} → N n → N (pred₁ n)
-- {-# ATP prove pred-N pred-N-ind-instance #-}

postulate pred-N : ∀ {n} → N n → N (pred₁ n)
{-# ATP prove pred-N pred-N-ind-instance N→0∨S #-}

+-N-ind-instance :
  ∀ {n} →
  N (zero + n) →
  (∀ {m} → N (m + n) → N (succ₁ m + n)) →
  ∀ {m} → N m → N (m + n)
+-N-ind-instance {n} = N-ind (λ i → N (i + n))

postulate +-N : ∀ {m n} → N m → N n → N (m + n)
{-# ATP prove +-N +-N-ind-instance #-}

∸-N-ind-instance :
  ∀ {m} →
  N (m ∸ zero) →
  (∀ {n} → N (m ∸ n) → N (m ∸ succ₁ n)) →
  ∀ {n} → N n → N (m ∸ n)
∸-N-ind-instance {n} = N-ind (λ i → N (n ∸ i))

postulate ∸-N : ∀ {m n} → N m → N n → N (m ∸ n)
{-# ATP prove ∸-N ∸-N-ind-instance pred-N #-}

*-N-ind-instance :
  ∀ {n} →
  N (zero * n) →
  (∀ {m} → N (m * n) → N (succ₁ m * n)) →
  ∀ {m} → N m → N (m * n)
*-N-ind-instance {n} = N-ind (λ i → N (i * n))

postulate *-N : ∀ {m n} → N m → N n → N (m * n)
{-# ATP prove *-N *-N-ind-instance +-N #-}

+-rightIdentity-ind-instance :
  zero + zero ≡ zero →
  (∀ {n} → n + zero ≡ n → succ₁ n + zero ≡ succ₁ n) →
  ∀ {n} → N n → n + zero ≡ n
+-rightIdentity-ind-instance = N-ind (λ i → i + zero ≡ i)

postulate +-rightIdentity : ∀ {n} → N n → n + zero ≡ n
{-# ATP prove +-rightIdentity +-rightIdentity-ind-instance #-}

+-assoc-ind-instance :
  ∀ {n} {o} →
  zero + n + o ≡ zero + (n + o) →
  (∀ {m} → m + n + o ≡ m + (n + o) → succ₁ m + n + o ≡ succ₁ m + (n + o)) →
  ∀ {m} → N m → m + n + o ≡ m + (n + o)
+-assoc-ind-instance {n} {o} = N-ind (λ i → i + n + o ≡ i + (n + o))

postulate +-assoc : ∀ {m} → N m → ∀ n o → m + n + o ≡ m + (n + o)
{-# ATP prove +-assoc +-assoc-ind-instance #-}

x+Sy≡S[x+y]-ind-instance :
  ∀ {n} →
  zero + succ₁ n ≡ succ₁ (zero + n) →
  (∀ {m} →
    m + succ₁ n ≡ succ₁ (m + n) → succ₁ m + succ₁ n ≡ succ₁ (succ₁ m + n)) →
  ∀ {m} → N m → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y]-ind-instance {n} = N-ind (λ i → i + succ₁ n ≡ succ₁ (i + n))

postulate x+Sy≡S[x+y] : ∀ {m} → N m → ∀ n → m + succ₁ n ≡ succ₁ (m + n)
{-# ATP prove x+Sy≡S[x+y] x+Sy≡S[x+y]-ind-instance #-}

+-comm-ind-instance :
  ∀ {n} →
  zero + n ≡ n + zero →
  (∀ {m} → m + n ≡ n + m → succ₁ m + n ≡ n + succ₁ m) →
  ∀ {m} → N m → m + n ≡ n + m
+-comm-ind-instance {n} = N-ind (λ i → i + n ≡ n + i)

postulate +-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
{-# ATP prove +-comm +-comm-ind-instance +-rightIdentity x+Sy≡S[x+y] #-}
