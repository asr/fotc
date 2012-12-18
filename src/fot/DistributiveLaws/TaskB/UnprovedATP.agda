------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DistributiveLaws.TaskB.UnprovedATP where

open import DistributiveLaws.Base

------------------------------------------------------------------------------
-- 25 July 2012: The ATPs could not prove the theorem (240 sec).
postulate
  prop₂ : ∀ u x y z → (x · y · (z · u)) ·
                      (( x · y · ( z · u)) · (x · z · (y · u))) ≡
                      x · z · (y · u)
{-# ATP prove prop₂ #-}
