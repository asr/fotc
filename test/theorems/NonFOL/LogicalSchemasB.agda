------------------------------------------------------------------------------
-- Testing the translation of the logical schemas
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --universal-quantified-propositional-functions #-}
{-# OPTIONS --without-K #-}

module NonFOL.LogicalSchemasB where

postulate D : Set

postulate id : {P : D → Set}{x : D} → P x → P x
{-# ATP prove id #-}
