------------------------------------------------------------------------------
-- Test the consistency of Draft.Mirror.Mirror
------------------------------------------------------------------------------

-- In the module Draft.Mirror.Mirror we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module Draft.Mirror.Mirror.ConsistencyTest where

open import LTC.Base

open import Draft.Mirror.Mirror

------------------------------------------------------------------------------

postulate
  impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
