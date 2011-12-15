------------------------------------------------------------------------------
-- Test the consistency of FOTC.Program.Collatz.Collatz
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module FOTC.Program.Collatz.Collatz we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module FOTC.Program.Collatz.Collatz.ConsistencyTest where

open import FOTC.Base
open import FOTC.Program.Collatz.Collatz

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
