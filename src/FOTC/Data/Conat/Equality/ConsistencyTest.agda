------------------------------------------------------------------------------
-- Test the consistency of FOTC.Data.Conat.Equality
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module FOTC.Data.Conat.Equality we declare Agda postulates
-- as FOL axioms. We test if it is possible to prove an unprovable
-- theorem from these axioms.

module FOTC.Data.Conat.Equality.ConsistencyTest where

open import FOTC.Base
open import FOTC.Data.Conat.Equality

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
