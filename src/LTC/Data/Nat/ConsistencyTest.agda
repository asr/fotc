------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.Nat
------------------------------------------------------------------------------

-- In the module LTC.Data.Nat we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module LTC.Data.Nat.ConsistencyTest where

open import LTC.Base

open import LTC.Data.Nat

------------------------------------------------------------------------------

postulate
  impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
