------------------------------------------------------------------------------
-- Properties related with lists of natural numbers (using equational
-- reasoning)
------------------------------------------------------------------------------

module LTC.Data.Nat.List.PropertiesER where

open import LTC.Base

open import LTC.Data.Nat.List.Type
  using ( ListN  -- The LTC list of natural numbers type.
        )
open import LTC.Data.List using ( _++_ )

------------------------------------------------------------------------------
-- See the ATP version.
postulate
  ++-ListN : {ds es : D} → ListN ds → ListN es → ListN (ds ++ es)
