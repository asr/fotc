------------------------------------------------------------------------------
-- Test the consistency of FOTC.Data.Nat
------------------------------------------------------------------------------

-- In the module FOTC.Data.Nat we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module FOTC.Data.Nat.ConsistencyTest where

open import FOTC.Base

open import FOTC.Data.Nat

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
