------------------------------------------------------------------------------
-- Inductive PA properties using the induction principle
------------------------------------------------------------------------------

module PA.Inductive.PropertiesByInductionATP where

open import PA.Inductive.Base

open import PA.Inductive.PropertiesByInduction

------------------------------------------------------------------------------

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = indℕ P P0 is m
  where
    P : ℕ → Set
    P i = i + n ≡ n + i
    {-# ATP definition P #-}

    P0 : P zero
    P0 = sym (+-rightIdentity n)

    postulate
      is : ∀ i → P i → P (succ i)
    {-# ATP prove is x+Sy≡S[x+y] #-}
