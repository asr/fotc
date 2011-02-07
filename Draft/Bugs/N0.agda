module Draft.Bugs.N0 where

open import LTC.Base
open import LTC.Data.Nat

-- TODO: Bug. The agda2atp tool does not translate the general hints.

{-# ATP hint zN #-}
{-# ATP hint sN #-}

postulate
 N0 : N zero
{-# ATP prove N0 #-}
