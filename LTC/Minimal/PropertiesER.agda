------------------------------------------------------------------------------
-- PCF terms properties
------------------------------------------------------------------------------

module LTC.Minimal.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER

open import LTC.Data.N
open import LTC.Relation.Equalities.PropertiesER

------------------------------------------------------------------------------
-- Closure properties

pred-N : {n : D} → N n → N (pred n)
pred-N zN          = subst (λ t → N t) (sym cP₁) zN
pred-N (sN {n} Nn) = subst (λ t → N t) (sym (cP₂ n)) Nn
