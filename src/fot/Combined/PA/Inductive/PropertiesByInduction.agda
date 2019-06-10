------------------------------------------------------------------------------
-- Inductive PA properties using the induction principle
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.PA.Inductive.PropertiesByInduction where

open import Combined.PA.Inductive.Base

------------------------------------------------------------------------------
-- Congruence properties

succCong : ∀ {m n} → m ≡ n → succ m ≡ succ n
succCong refl = refl

------------------------------------------------------------------------------

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = refl

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity n = ℕ-ind A A0 is n
  where
  A : ℕ → Set
  A i = i + zero ≡ i

  A0 : A zero
  A0 = refl

  is : ∀ i → A i → A (succ i)
  is i ih = succCong ih

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc m n o = ℕ-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + n + o ≡ i + (n + o)

  A0 : A zero
  A0 = refl

  is : ∀ i → A i → A (succ i)
  is i ih = succCong ih

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] m n = ℕ-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + succ n ≡ succ (i + n)

  A0 : A zero
  A0 = refl

  is : ∀ i → A i → A (succ i)
  is i ih = succCong ih

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = ℕ-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + n ≡ n + i
  {-# ATP definition A #-}

  A0 : A zero
  A0 = sym (+-rightIdentity n)

  postulate is : ∀ i → A i → A (succ i)
  -- TODO (21 November 2014). See Apia issue 16
  -- {-# ATP prove is x+Sy≡S[x+y] #-}
