------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.Bool
------------------------------------------------------------------------------

-- In the module LTC.Data.Bool we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module LTC.Data.Bool.ConsistencyTest where

open import LTC.Base

open import LTC.Data.Bool

------------------------------------------------------------------------------

postulate
  impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
