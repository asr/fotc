------------------------------------------------------------------------------
-- Testing the translation of the logical schemas
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.FOL.LogicalSchemas1 where

postulate D : Set

postulate id : {P : Set} → P → P
{-# ATP prove id #-}
