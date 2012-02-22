-- Tested with FOT on 22 February 2012.

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.PA.Axiomatic.Mendelson.AssocAdditionATP where

open import PA.Axiomatic.Mendelson.Base

postulate +-leftCong : ∀ {m n o} → m ≐ n → m + o ≐ n + o

+-asocc : ∀ m n o → m + n + o ≐ m + (n + o)
+-asocc m n o = S₉ P P0 is m
  where
  P : M → Set
  P i = i + n + o ≐ i + (n + o)
  {-# ATP definition P #-}

  postulate P0 : P zero
  -- {-# ATP prove P0 +-leftCong #-}

  -- (2012-02-22) E 1.4. CPU time limit exceeded, terminating (180 sec).
  -- (2012-02-22) Metis 2.3 (release 20110926). SZS status Unknown (180 sec).
  -- (2012-02-22) Vampire 0.6 (revision 903). Time limit reached! (180 sec).
  postulate is : ∀ i → P i → P (succ i)
  {-# ATP prove is +-leftCong #-}
