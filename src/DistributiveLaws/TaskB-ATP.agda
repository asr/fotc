------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation
------------------------------------------------------------------------------

module DistributiveLaws.TaskB-ATP where

open import DistributiveLaws.Base

------------------------------------------------------------------------------

postulate
  taskB : ∀ u x y z → (x · y · (z · u)) ·
                      (( x · y · ( z · u)) · (x · z · (y · u))) ≡
                      x · z · (y · u)
  -- E 1.2:                         No-success due to timeout (300 sec).
  -- Equinox 5.0alpha (2010-06-29): No-success due to timeout (300 sec).
  -- Metis 2.3 (release 20101019):  No-success due to timeout (300 sec).
  -- Vampire 0.6 (revision 903):    (Default) memory limit (using timeout 300 sec).
-- {-# ATP prove taskB #-}
