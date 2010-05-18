------------------------------------------------------------------------------
-- Functions on equalities
------------------------------------------------------------------------------

module LTC.Relation.Equalities.Properties where

open import LTC.Minimal

------------------------------------------------------------------------------

¬S≡0 : {d : D} → ¬ (succ d ≡ zero)
¬S≡0 S≡0 = ⊥-elim prf
  where
    -- The proof uses the axiom 0≠S
    postulate prf : ⊥
    {-# ATP prove prf #-}
