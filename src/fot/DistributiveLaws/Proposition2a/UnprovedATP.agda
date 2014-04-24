------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Proposition 2a
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DistributiveLaws.Proposition2a.UnprovedATP where

open import DistributiveLaws.Base

------------------------------------------------------------------------------
-- 31 July 2013: The ATPs could not prove the theorem (240 sec).
postulate
  proposition2a :
    ∀ u x y z →
    (x · y · (z · u)) · ((x · y · (z · u)) · (x · z · (y · u))) ≡
      x · z · (y · u)
{-# ATP prove proposition2a #-}
