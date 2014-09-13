------------------------------------------------------------------------------
-- Inductive PA properties using the induction principle
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module PA.Inductive.PropertiesByInductionATP where

open import PA.Inductive.Base
open import PA.Inductive.PropertiesByInduction

------------------------------------------------------------------------------

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = ℕ-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + n ≡ n + i
  {-# ATP definition A #-}

  A0 : A zero
  A0 = sym (+-rightIdentity n)

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is x+Sy≡S[x+y] #-}
