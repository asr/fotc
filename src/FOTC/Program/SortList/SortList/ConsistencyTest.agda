------------------------------------------------------------------------------
-- Test the consistency of FOTC.Program.SortList.SortList
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module FOTC.Program.SortList.SortList we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module FOTC.Program.SortList.SortList.ConsistencyTest where

open import FOTC.Base
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
