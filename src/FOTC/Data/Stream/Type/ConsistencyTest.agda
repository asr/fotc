------------------------------------------------------------------------------
-- Test the consistency of FOTC.Data.Stream.Type
------------------------------------------------------------------------------

-- In the module FOTC.Data.Stream.Type we declare Agda postulates as
-- FOL axioms. We test if it is possible to prove an unprovable
-- theorem from these axioms.

module FOTC.Data.Stream.Type.ConsistencyTest where

open import FOTC.Base
open import FOTC.Data.Stream.Type

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
