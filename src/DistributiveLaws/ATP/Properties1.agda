------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation (using the ATPs)
------------------------------------------------------------------------------

module DistributiveLaws.ATP.Properties1 where

open import DistributiveLaws.Base

------------------------------------------------------------------------------

postulate
  Stanovsky : ∀ u x y z → (x ∙ y ∙ (z ∙ u)) ∙
                          (( x ∙ y ∙ ( z ∙ u)) ∙ (x ∙ z ∙ (y ∙ u))) ≡
                          x ∙ z ∙ (y ∙ u)
  -- E 1.2 no-success due to timeout (300 sec).
  -- Equinox 5.0alpha (2010-06-29) no-success due to timeout (300 sec).
  -- Metis 2.3 (release 20101019) no-success due to timeout (300 sec).
  -- {-# ATP prove Stanovsky #-}
