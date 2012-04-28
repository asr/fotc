------------------------------------------------------------------------------
-- Test the consistency of Draft.FO-LTC-PCF.Base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module Draft.FO-LTC-PCF.Base we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module Draft.FO-LTC-PCF.Base.ConsistencyTest where

open import Draft.FO-LTC-PCF.Base

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
