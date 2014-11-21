------------------------------------------------------------------------------
-- Test the consistency of FOTC.Data.Conat.Equality.Type
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module FOTC.Data.Conat.Equality.Type we declare Agda postulates
-- as first-order logic axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module FOTC.Data.Conat.Equality.Consistency.Axioms where

open import FOTC.Base
open import FOTC.Data.Conat.Equality.Type

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
