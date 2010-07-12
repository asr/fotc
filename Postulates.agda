------------------------------------------------------------------------------
-- Some stuff to be proved
------------------------------------------------------------------------------

module Postulates where

open import LTC.Minimal

open import Examples.SortList.SortList


open import LTC.Data.Bool
open import LTC.Data.Nat.Type
open import LTC.Data.Nat.List

------------------------------------------------------------------------------

-- The following postulates are requeried due to our temporal
-- definition of lists of natural numbers.

postulate
  ++-ListOrd-aux₁ : {item is js : D} → N item → List is → List js →
                    ≤-ItemList item is ≡ true →
                    ≤-Lists is js ≡ true →
                    ≤-ItemList item js ≡ true
postulate
  []-N : N []

postulate
  ++-List : {ds es : D} → List ds → List es → List (ds ++ es)
