------------------------------------------------------------------------------
-- Test the consistency of FOTC.Base.List
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module FOTC.Base.List we declare Agda postulates as
-- first-order logic axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module FOTC.Base.List.Consistency.Axioms where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
