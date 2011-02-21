------------------------------------------------------------------------------
-- Test the consistency of LTC-PCF.Base
------------------------------------------------------------------------------

-- In the module LTC-PCF.Base we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module LTC-PCF.Base.ConsistencyTest where

open import LTC-PCF.Base

------------------------------------------------------------------------------

postulate
  impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
