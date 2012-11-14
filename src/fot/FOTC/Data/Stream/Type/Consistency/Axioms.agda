------------------------------------------------------------------------------
-- Test the consistency of FOTC.Data.Stream.Type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module FOTC.Data.Stream.Type we declare Agda postulates as
-- first-order logic axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module FOTC.Data.Stream.Type.Consistency.Axioms where

open import FOTC.Base
open import FOTC.Data.Stream.Type

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
