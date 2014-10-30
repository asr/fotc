------------------------------------------------------------------------------
-- Inductive PA properties
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module PA.Inductive.PropertiesATP where

open import PA.Inductive.Base

------------------------------------------------------------------------------

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity zero     = refl
+-rightIdentity (succ n) = prf (+-rightIdentity n)
  where postulate prf : n + zero ≡ n → succ n + zero ≡ succ n
        {-# ATP prove prf #-}

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] zero     _ = refl
x+Sy≡S[x+y] (succ m) n = prf (x+Sy≡S[x+y] m n)
  where postulate prf : m + succ n ≡ succ (m + n) →
                        succ m + succ n ≡ succ (succ m + n)
        {-# ATP prove prf #-}

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero     n = sym (+-rightIdentity n)
+-comm (succ m) n = prf (+-comm m n)
  where postulate prf : m + n ≡ n + m → succ m + n ≡ n + succ m
        {-# ATP prove prf x+Sy≡S[x+y] #-}
