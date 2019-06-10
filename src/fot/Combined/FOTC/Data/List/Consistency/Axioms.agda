------------------------------------------------------------------------------
-- Test the consistency of Combined.FOTC.Data.List
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module Combined.FOTC.Data.List we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module Combined.FOTC.Data.List.Consistency.Axioms where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.List

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
