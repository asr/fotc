------------------------------------------------------------------------------
-- Unproven PA properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Axiomatic.Mendelson.Properties.UnprovedATP where

open import PA.Axiomatic.Mendelson.Base
open import PA.Axiomatic.Mendelson.PropertiesATP

------------------------------------------------------------------------------

+-asocc : ∀ m n o → m + n + o ≈ m + (n + o)
+-asocc m n o = S₉ A A0 is m
  where
  A : M → Set
  A i = i + n + o ≈ i + (n + o)
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 +-leftCong #-}

  -- 18 December 2012: The ATPs could not prove the theorem (240 sec).
  --
  -- After the addition of the inequality _≉_, no ATP proves the
  -- theorem. Before it, only Equinox 5.0alpha (2010-06-29) had proved
  -- the theorem.
  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is +-leftCong #-}
