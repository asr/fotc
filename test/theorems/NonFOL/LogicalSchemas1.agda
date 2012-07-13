------------------------------------------------------------------------------
-- Testing the translation of the logical schemas
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --universal-quantified-formula #-}
{-# OPTIONS --without-K #-}

module NonFOL.LogicalSchemas1 where

postulate D : Set

postulate id : {P : Set} → P → P
{-# ATP prove id #-}
