------------------------------------------------------------------------------
-- Common (interactive and automatic) properties using the induction principle
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Inductive.PropertiesByInduction where

open import PA.Inductive.Base

------------------------------------------------------------------------------

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = refl

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity n = PA-ind P P0 is n
  where
  P : M → Set
  P i = i + zero ≡ i

  P0 : P zero
  P0 = refl

  is : ∀ i → P i → P (succ i)
  is i Pi = cong succ Pi

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc m n o = PA-ind P P0 is m
  where
  P : M → Set
  P i = i + n + o ≡ i + (n + o)

  P0 : P zero
  P0 = refl

  is : ∀ i → P i → P (succ i)
  is i Pi = cong succ Pi

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] m n = PA-ind P P0 is m
  where
  P : M → Set
  P i = i + succ n ≡ succ (i + n)

  P0 : P zero
  P0 = refl

  is : ∀ i → P i → P (succ i)
  is i Pi = cong succ Pi
