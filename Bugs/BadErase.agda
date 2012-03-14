------------------------------------------------------------------------------
-- The translation is badly erasing the universal quantification
------------------------------------------------------------------------------

-- Found on 14 March 2012.

module Bugs.BadErase where

postulate
  D : Set
  A : Set

postulate bad : ((x : D) → A) → A
{-# ATP prove bad #-}
