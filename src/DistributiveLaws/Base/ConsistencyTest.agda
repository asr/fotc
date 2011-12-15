------------------------------------------------------------------------------
-- Test the consistency of GroupTheory.Groupoids.Base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module DistributiveLaws.Base we declare Agda postulates
-- as FOL axioms. We test if it is possible to prove an unprovable
-- theorem from these axioms.

module DistributiveLaws.Base.ConsistencyTest where

open import DistributiveLaws.Base

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
