-- Tested with FOT on 02 March 2012.

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.PA.Axiomatic.Mendelson.AssocAdditionATP where

open import PA.Axiomatic.Mendelson.Base

postulate +-leftCong : ∀ {m n o} → m ≐ n → m + o ≐ n + o

+-asocc : ∀ m n o → m + n + o ≐ m + (n + o)
+-asocc m n o = S₉ A A0 is m
  where
  A : M → Set
  A i = i + n + o ≐ i + (n + o)
  {-# ATP definition A #-}

  postulate A0 : A zero
  -- {-# ATP prove P0 +-leftCong #-}

  -- 2012-03-02: Only Equinox 5.0alpha (2010-06-29) proved the theorem (180 sec).
  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is +-leftCong #-}
