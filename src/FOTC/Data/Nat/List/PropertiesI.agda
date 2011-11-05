------------------------------------------------------------------------------
-- Properties related with lists of natural numbers
------------------------------------------------------------------------------

module FOTC.Data.Nat.List.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.List

------------------------------------------------------------------------------
-- See the ATP version.
postulate ++-ListN : ∀ {ds es} → ListN ds → ListN es → ListN (ds ++ es)
