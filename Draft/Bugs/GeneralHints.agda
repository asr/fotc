module Draft.Bugs.GeneralHints where

open import LTC.Base
open import LTC.Data.Nat

-- TODO: Bug. The agda2atp tool does not translate the general hints

-- {-# ATP hint zN #-}
-- {-# ATP hint sN #-}

-- because they are not defined in the file LTC.Data.Nat.Type.

postulate
 N0 : N zero
{-# ATP prove N0 #-}
