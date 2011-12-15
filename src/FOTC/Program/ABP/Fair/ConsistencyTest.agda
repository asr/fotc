------------------------------------------------------------------------------
-- Test the consistency of FOTC.Program.ABP.Fair
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module FOTC.Program.ABP.Fair we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module FOTC.Program.ABP.Fair.ConsistencyTest where

open import FOTC.Base
open import FOTC.Program.ABP.Fair

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
