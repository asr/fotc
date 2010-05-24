------------------------------------------------------------------------------
-- Functions on equalities
------------------------------------------------------------------------------

module LTC.Relation.Equalities.Properties where

open import LTC.Minimal

------------------------------------------------------------------------------

postulate
  ¬S≡0 : {d : D} → ¬ (succ d ≡ zero)
{-# ATP prove ¬S≡0 #-}
