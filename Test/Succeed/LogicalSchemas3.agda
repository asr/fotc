------------------------------------------------------------------------------
-- Testing the translation of the logical schemas
------------------------------------------------------------------------------

module Test.Succeed.LogicalSchemas3 where

postulate
  D   : Set

postulate id : {P : Set} → P → P
{-# ATP prove id #-}
