------------------------------------------------------------------------------
-- Test the consistency of PA.Axiomatic.Standard.Base
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In the module PA.Axiomatic.Standard.Base we declare Agda postulates
-- as first-order logic axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module PA.Axiomatic.Standard.Base.Consistency.Axioms where

open import PA.Axiomatic.Standard.Base

------------------------------------------------------------------------------

postulate impossible : (m n : ℕ) → m ≡ n
{-# ATP prove impossible #-}
