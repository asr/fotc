------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DistributiveLaws.TaskB-ATP where

open import DistributiveLaws.Base

------------------------------------------------------------------------------

postulate
  prop₂ : ∀ u x y z → (x · y · (z · u)) ·
                      (( x · y · ( z · u)) · (x · z · (y · u))) ≡
                      x · z · (y · u)
-- E 1.4: CPU time limit exceeded, terminating (180 sec).
-- Equinox 5.0alpha (2010-06-29): TIMEOUT (300 seconds)
-- Metis 2.3 (release 20110926): SZS status Unknown (using timeout 300 sec).
-- SPASS 3.7: Ran out of time (using timeout 300 sec).
-- Vampire 0.6 (revision 903): (Default) memory limit (using timeout 300 sec).
-- {-# ATP prove prop₂ #-}
