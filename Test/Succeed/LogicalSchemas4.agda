------------------------------------------------------------------------------
-- Testing the translation of the logical schemas
------------------------------------------------------------------------------

module Test.Succeed.LogicalSchemas4 where

postulate
  D   : Set

postulate id : {P : D → Set}{x : D} → P x → P x
{-# ATP prove id #-}
