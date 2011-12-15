------------------------------------------------------------------------------
-- Test the consistency of FOTC.Base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module FOTC.Base we declare Agda postulates as FOL axioms. We
-- test if it is possible to prove an unprovable theorem from these
-- axioms.

module FOTC.Base.ConsistencyTest where

open import FOTC.Base

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
