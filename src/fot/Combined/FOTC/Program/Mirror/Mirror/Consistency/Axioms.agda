------------------------------------------------------------------------------
-- Test the consistency of Combined.FOTC.Program.Mirror.Mirror
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module Combined.FOTC.Program.Mirror.Mirror we declare Agda
-- postulates as first-order logic axioms. We test if it is possible
-- to prove an unprovable theorem from these axioms.

module Combined.FOTC.Program.Mirror.Mirror.Consistency.Axioms where

open import Combined.FOTC.Base
open import Combined.FOTC.Program.Mirror.Mirror

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
