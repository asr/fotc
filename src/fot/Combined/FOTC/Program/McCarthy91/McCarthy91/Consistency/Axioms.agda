------------------------------------------------------------------------------
-- Test the consistency of Combined.FOTC.Program.McCarthy91.McCarthy91
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module Combined.FOTC.Program.McCarthy91.McCarthy91 we declare
-- Agda postulates as first-order logic axioms. We test if it is
-- possible to prove an unprovable theorem from these axioms.

module Combined.FOTC.Program.McCarthy91.McCarthy91.Consistency.Axioms where

open import Combined.FOTC.Base
open import Combined.FOTC.Program.McCarthy91.McCarthy91

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
