------------------------------------------------------------------------------
-- Functions on equalities
------------------------------------------------------------------------------

module LTC.Relation.Equalities.Properties where

open import LTC.Minimal

------------------------------------------------------------------------------

postulate
  sym : {x y : D} → x ≡ y → y ≡ x
{-# ATP prove sym #-}

postulate
  trans : {x y z : D} → x ≡ y → y ≡ z → x ≡ z

postulate
  ¬S≡0 : {d : D} → ¬ (succ d ≡ zero)
{-# ATP prove ¬S≡0 #-}

x≡y→Sx≡Sy : {m n : D} → m ≡ n → succ m ≡ succ n
x≡y→Sx≡Sy refl = refl
