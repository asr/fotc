------------------------------------------------------------------------------
-- Test the consistency of GroupTheory.Groupoids.Base
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module DistributiveLaws.Base we declare Agda postulates as
-- first-order logic axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module DistributiveLaws.Base.Consistency.Axioms where

open import DistributiveLaws.Base

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
