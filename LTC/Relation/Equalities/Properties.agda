------------------------------------------------------------------------------
-- Functions on equalities
------------------------------------------------------------------------------

module LTC.Relation.Equalities.Properties where

open import LTC.Minimal

------------------------------------------------------------------------------

¬S≡0 : {d : D} → ¬ (succ d ≡ zero)
¬S≡0 S≡0 = ⊥-elim prf
  where
    postulate
      -- The proof uses the axiom 0≠S
      prf : ⊥
    {-# ATP prove prf #-}
