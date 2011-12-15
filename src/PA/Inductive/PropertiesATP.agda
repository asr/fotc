------------------------------------------------------------------------------
-- Inductive PA properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Inductive.PropertiesATP where

open import PA.Inductive.Base

open import PA.Inductive.Properties

------------------------------------------------------------------------------

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero     n = sym (+-rightIdentity n)
+-comm (succ m) n = prf (+-comm m n)
  where
  postulate prf : m + n ≡ n + m →  -- IH.
                  succ m + n ≡ n + succ m
  {-# ATP prove prf x+Sy≡S[x+y] #-}
