------------------------------------------------------------------------------
-- Test the consistency of FOTC.Data.Bool
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module FOTC.Data.Bool we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module FOTC.Data.Bool.ConsistencyTest where

open import FOTC.Base
open import FOTC.Data.Bool

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
