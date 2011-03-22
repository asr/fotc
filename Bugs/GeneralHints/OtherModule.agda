module Bugs.GeneralHints.OtherModule where

open import Bugs.GeneralHints

-- The agda2atp tool does not translate the general hint because they
-- are not defined in the module Bugs.GeneralHints.

-- General hint
{-# ATP hint zN #-}

postulate
  N0 : N zero
{-# ATP prove N0 #-}
