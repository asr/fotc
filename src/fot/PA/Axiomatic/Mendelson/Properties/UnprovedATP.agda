------------------------------------------------------------------------------
-- Unproven PA properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module PA.Axiomatic.Mendelson.Properties.UnprovedATP where

open import PA.Axiomatic.Mendelson.Base
open import PA.Axiomatic.Mendelson.PropertiesATP

------------------------------------------------------------------------------

+-asocc : ∀ m n o → m + n + o ≈ m + (n + o)
+-asocc m n o = S₉ A A0 is m
  where
  A : ℕ → Set
  A i = i + n + o ≈ i + (n + o)
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 +-leftCong #-}

  -- 25 November 2013: Vampire 0.6 (revision 903) proves the theorem
  -- using the --mode casc option and a time out of 300 sec.

  -- 06 January 2016: The ATPs could not prove the theorem (240 sec).
  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is +-leftCong #-}
