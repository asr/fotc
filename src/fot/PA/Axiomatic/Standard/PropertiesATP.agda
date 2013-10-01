------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Axiomatic.Standard.PropertiesATP where

open import PA.Axiomatic.Standard.Base

------------------------------------------------------------------------------
-- Congruence properties

postulate succCong : ∀ {m n} → m ≡ n → succ m ≡ succ n
{-# ATP prove succCong #-}

postulate +-leftCong : ∀ {m n o} → m ≡ n → m + o ≡ n + o
{-# ATP prove +-leftCong #-}

postulate +-rightCong : ∀ {m n o} → n ≡ o → m + n ≡ m + o
{-# ATP prove +-rightCong #-}

------------------------------------------------------------------------------

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity = PA₃

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity = PA-ind A A0 is
  where
  A : ℕ → Set
  A i = i + zero ≡ i
  {-# ATP definition A #-}

  A0 : A zero
  A0 = +-leftIdentity zero

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is #-}

+-asocc : ∀ m n o → m + n + o ≡ m + (n + o)
+-asocc m n o = PA-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + n + o ≡ i + (n + o)
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 #-}

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is #-}

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] m n = PA-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + succ n ≡ succ (i + n)
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 #-}

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is #-}

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = PA-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + n ≡ n + i
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 +-rightIdentity #-}

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is x+Sy≡S[x+y] #-}
