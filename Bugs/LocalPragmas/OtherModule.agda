module Bugs.LocalPragmas.OtherModule where

open import Bugs.LocalPragmas

-- The program agda2atp does not translate the ATP pragmas because
-- they are not defined in the module Bugs.GeneralHints.

{-# ATP axiom zN #-}

postulate
  N0 : N zero
{-# ATP prove N0 #-}
