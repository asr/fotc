------------------------------------------------------------------------------
-- Test the consistency of FOTC.Program.Division.Division
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module FOTC.Program.Division.Division we declare Agda
-- postulates as first-order logic axioms. We test if it is possible
-- to prove an unprovable theorem from these axioms.

module FOTC.Program.Division.Division.Consistency.Axioms where

open import FOTC.Base
open import FOTC.Program.Division.Division

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
