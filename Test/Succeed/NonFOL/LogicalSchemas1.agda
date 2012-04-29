------------------------------------------------------------------------------
-- Testing the translation of the logical schemas
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Requires option @--non-fol-formula@.

module Test.Succeed.NonFOL.LogicalSchemas1 where

postulate D : Set

postulate id : {P : Set} → P → P
{-# ATP prove id #-}
