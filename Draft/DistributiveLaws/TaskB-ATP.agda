------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation
------------------------------------------------------------------------------

module Draft.DistributiveLaws.TaskB-ATP where

open import DistributiveLaws.Base

------------------------------------------------------------------------------

postulate
  prop₂ : ∀ u x y z → (x · y · (z · u)) ·
                      (( x · y · ( z · u)) · (x · z · (y · u))) ≡
                      x · z · (y · u)
{-# ATP prove prop₂ #-}
