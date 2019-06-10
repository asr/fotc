------------------------------------------------------------------------------
-- Test the consistency of Combined.FOTC.Base.List
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module Combined.FOTC.Base.List we declare Agda postulates as
-- first-order logic axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module Combined.FOTC.Base.List.Consistency.Axioms where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
