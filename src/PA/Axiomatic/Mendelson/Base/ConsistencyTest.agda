------------------------------------------------------------------------------
-- Test the consistency of PA.Axiomatic.Mendelson.Base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module PA.Axiomatic.Mendelson.Base we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module PA.Axiomatic.Mendelson.Base.ConsistencyTest where

open import PA.Axiomatic.Mendelson.Base

------------------------------------------------------------------------------

postulate impossible : (m n : M) → m ≐ n
{-# ATP prove impossible #-}
