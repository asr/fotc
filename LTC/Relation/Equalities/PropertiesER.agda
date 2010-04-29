------------------------------------------------------------------------------
-- Functions on equalities using equational reasoning
------------------------------------------------------------------------------

module LTC.Relation.Equalities.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER

open import MyStdLib.Function

------------------------------------------------------------------------------

¬S≡0 : {n : D} → ¬ (succ n ≡ zero)
¬S≡0 S≡0 = 0≠S $ sym S≡0
