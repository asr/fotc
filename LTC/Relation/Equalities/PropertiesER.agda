------------------------------------------------------------------------------
-- Functions on equalities using equational reasoning
------------------------------------------------------------------------------

module LTC.Relation.Equalities.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER

open import MyStdLib.Function

------------------------------------------------------------------------------

sym : {x y : D} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : D} → x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z

¬S≡0 : {n : D} → ¬ (succ n ≡ zero)
¬S≡0 S≡0 = 0≠S $ sym S≡0

x≡y→Sx≡Sy : {m n : D} → m ≡ n → succ m ≡ succ n
x≡y→Sx≡Sy refl = refl
