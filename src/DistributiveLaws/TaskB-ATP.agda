------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation
------------------------------------------------------------------------------

module DistributiveLaws.TaskB-ATP where

open import DistributiveLaws.Base

------------------------------------------------------------------------------

postulate
  prop₂ : ∀ u x y z → (x · y · (z · u)) ·
                      (( x · y · ( z · u)) · (x · z · (y · u))) ≡
                      x · z · (y · u)
  -- E 1.3: CPU time limit exceeded (180 sec)
  -- E 1.3: CPU time limit exceeded (300 sec)
  -- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds)
  -- Equinox 5.0alpha (2010-06-29): TIMEOUT (300 seconds)
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 300 sec).
  -- Vampire 0.6 (revision 903): (Default) memory limit (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): (Default) memory limit (using timeout 300 sec).
-- {-# ATP prove prop₂ #-}
