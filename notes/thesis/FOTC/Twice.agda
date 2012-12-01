------------------------------------------------------------------------------
-- Twice funcion
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Twice where

open import FOTC.Base

------------------------------------------------------------------------------

module HigherOrder where

  -- We cannot translate this function as a definition because it is
  -- higher-order.
  twice : (D → D) → D → D
  twice f x = f (f x)
  -- {-# ATP definition twice #-}

  postulate twice-succ : ∀ n → twice succ₁ n ≡ succ₁ (succ₁ n)
  -- {-# ATP prove twice-succ #-}

module FirstOrder where

  twice :  D → D → D
  twice f x = f · (f · x)
  {-# ATP definition twice #-}

  postulate twice-succ : ∀ n → twice succ n ≡ succ · (succ · n)
  {-# ATP prove twice-succ #-}
