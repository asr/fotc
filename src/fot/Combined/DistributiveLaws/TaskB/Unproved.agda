------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Task B
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.DistributiveLaws.TaskB.Unproved where

open import Combined.DistributiveLaws.Base

------------------------------------------------------------------------------
-- 2018-06-28: The ATPs could not prove the theorem (300 sec).
postulate
  prop₂ : ∀ u x y z →
          (x · y · (z · u)) · ((x · y · (z · u)) · (x · z · (y · u))) ≡
            x · z · (y · u)
{-# ATP prove prop₂ #-}
