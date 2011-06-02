------------------------------------------------------------------------------
-- Properties related with lists of natural numbers
------------------------------------------------------------------------------

module FOTC.Data.Nat.List.PropertiesI where

open import FOTC.Base

open import FOTC.Data.Nat.List.Type
  using ( ListN  -- The FOTC list of natural numbers type.
        )
open import FOTC.Data.List using ( _++_ )

------------------------------------------------------------------------------
-- See the ATP version.
postulate ++-ListN : ∀ {ds es} → ListN ds → ListN es → ListN (ds ++ es)
