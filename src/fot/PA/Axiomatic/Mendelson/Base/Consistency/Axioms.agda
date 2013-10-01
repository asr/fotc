------------------------------------------------------------------------------
-- Test the consistency of PA.Axiomatic.Mendelson.Base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module PA.Axiomatic.Mendelson.Base we declare Agda
-- postulates as first-order logic axioms. We test if it is possible
-- to prove an unprovable theorem from these axioms.

module PA.Axiomatic.Mendelson.Base.Consistency.Axioms where

open import PA.Axiomatic.Mendelson.Base

------------------------------------------------------------------------------

postulate impossible : (m n : ℕ) → m ≈ n
{-# ATP prove impossible #-}
