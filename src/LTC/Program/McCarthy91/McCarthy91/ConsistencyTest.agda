------------------------------------------------------------------------------
-- Test the consistency of LTC.Program.McCarthy91.McCarthy91
------------------------------------------------------------------------------

-- In the module LTC.Program.McCarthy91.McCarthy91 we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module LTC.Program.McCarthy91.McCarthy91.ConsistencyTest where

open import LTC.Base

open import LTC.Program.McCarthy91.McCarthy91

------------------------------------------------------------------------------

postulate
  impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
