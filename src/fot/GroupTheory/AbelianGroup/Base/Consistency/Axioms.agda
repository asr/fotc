------------------------------------------------------------------------------
-- Test the consistency of GroupTheory.AbelianGroup.Base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module GroupTheory.AbelianGroup.Base we declare Agda
-- postulates as first-order logic axioms. We test if it is possible
-- to prove an unprovable theorem from these axioms.

module GroupTheory.AbelianGroup.Base.Consistency.Axioms where

open import GroupTheory.AbelianGroup.Base

------------------------------------------------------------------------------

postulate impossible : (d e : G) → d ≡ e
{-# ATP prove impossible #-}
