------------------------------------------------------------------------------
-- Test the consistency of FOTC.Data.Stream.Equality
------------------------------------------------------------------------------

-- In the module FOTC.Data.Stream.Equality we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module FOTC.Data.Stream.Equality.ConsistencyTest where

open import FOTC.Base

open import FOTC.Data.Stream.Equality

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
