------------------------------------------------------------------------------
-- Some stuff to be proved
------------------------------------------------------------------------------

module Postulates where

open import LTC.Minimal

open import Examples.SortList.SortList


open import LTC.Data.Bool
open import LTC.Data.List
open import LTC.Data.Nat.Type
open import LTC.Data.Nat.List.Type

------------------------------------------------------------------------------
-- TODO: Remove the postulates.

postulate
  ++-ListOrd-aux₁ : {item is js : D} → N item → ListN is → ListN js →
                    ≤-ItemList item is ≡ true →
                    ≤-Lists is js ≡ true →
                    ≤-ItemList item js ≡ true
