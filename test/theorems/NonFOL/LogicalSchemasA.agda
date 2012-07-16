------------------------------------------------------------------------------
-- Testing the translation of the logical schemas
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --universal-quantified-formulas #-}
{-# OPTIONS --without-K #-}

module NonFOL.LogicalSchemasA where

postulate D : Set

postulate id : {P : Set} → P → P
{-# ATP prove id #-}
