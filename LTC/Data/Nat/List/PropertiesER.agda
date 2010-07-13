------------------------------------------------------------------------------
-- Properties related with lists of natural numbers
-- (using equational reasoning )
------------------------------------------------------------------------------

module LTC.Data.Nat.List.PropertiesER where

open import LTC.Minimal

open import LTC.Data.Nat
open import LTC.Data.Nat.List.Type
open import LTC.Data.List

------------------------------------------------------------------------------
-- See ATP version.
postulate
  ++-ListN : {ds es : D} → ListN ds → ListN es → ListN (ds ++ es)
