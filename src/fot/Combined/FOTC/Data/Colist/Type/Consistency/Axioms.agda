------------------------------------------------------------------------------
-- Test the consistency of Combined.FOTC.Data.Colist.Type
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module Combined.FOTC.Data.Colist.Type we declare Agda postulates as
-- first-order logic axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module Combined.FOTC.Data.Colist.Type.Consistency.Axioms where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Colist.Type

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
