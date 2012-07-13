------------------------------------------------------------------------------
-- Testing the Agda pragma --universal-quantified-formulas
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Fails because requires the above pragma.

module PragmaRequired1 where

postulate D : Set

postulate id : {P : Set} → P → P
{-# ATP prove id #-}
