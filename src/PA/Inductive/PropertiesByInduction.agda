------------------------------------------------------------------------------
-- Common (interactive and automatic) properties using the induction principle
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Inductive.PropertiesByInduction where

open import PA.Inductive.Base

------------------------------------------------------------------------------
-- Congruence properties

succ-cong : ∀ {m n} → m ≡ n → succ m ≡ succ n
succ-cong refl = refl

------------------------------------------------------------------------------

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = refl

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity n = PA-ind A A0 is n
  where
  A : M → Set
  A i = i + zero ≡ i

  A0 : A zero
  A0 = refl

  is : ∀ i → A i → A (succ i)
  is i ih = succ-cong ih

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc m n o = PA-ind A A0 is m
  where
  A : M → Set
  A i = i + n + o ≡ i + (n + o)

  A0 : A zero
  A0 = refl

  is : ∀ i → A i → A (succ i)
  is i ih = succ-cong ih

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] m n = PA-ind A A0 is m
  where
  A : M → Set
  A i = i + succ n ≡ succ (i + n)

  A0 : A zero
  A0 = refl

  is : ∀ i → A i → A (succ i)
  is i ih = succ-cong ih
