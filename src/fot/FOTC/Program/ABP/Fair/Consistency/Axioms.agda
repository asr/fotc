------------------------------------------------------------------------------
-- Test the consistency of FOTC.Program.ABP.Fair.Type
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module FOTC.Program.ABP.Fair.Type we declare Agda postulates
-- as first-order logic axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module FOTC.Program.ABP.Fair.Consistency.Axioms where

open import FOTC.Base
open import FOTC.Program.ABP.Fair.Type

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
