------------------------------------------------------------------------------
-- Common (interactive and automatic) inductive PA properties using
-- the induction principle
------------------------------------------------------------------------------

module PA.Inductive.PropertiesByInduction where

open import PA.Inductive.Base

------------------------------------------------------------------------------

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = refl

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity n = indℕ P P0 iStep n
  where
    P : ℕ → Set
    P i = i + zero ≡ i

    P0 : P zero
    P0 = refl

    iStep : ∀ i → P i → P (succ i)
    iStep i Pi = cong succ Pi

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc m n o = indℕ P P0 iStep m
  where
    P : ℕ → Set
    P i = i + n + o ≡ i + (n + o)

    P0 : P zero
    P0 = refl

    iStep : ∀ i → P i → P (succ i)
    iStep i Pi = cong succ Pi

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] m n = indℕ P P0 iStep m
  where
    P : ℕ → Set
    P i = i + succ n ≡ succ (i + n)

    P0 : P zero
    P0 = refl

    iStep : ∀ i → P i → P (succ i)
    iStep i Pi = cong succ Pi
