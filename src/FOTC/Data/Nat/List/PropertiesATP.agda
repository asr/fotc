------------------------------------------------------------------------------
-- Properties related with lists of natural numbers
------------------------------------------------------------------------------

module FOTC.Data.Nat.List.PropertiesATP where

open import FOTC.Base

open import Common.Function using ( _$_ )

open import FOTC.Data.Nat.List.Type
  using ( ListN ; consLN ; nilLN  -- The FOTC list of natural numbers type.
        )
open import FOTC.Data.List using ( _++_ )

------------------------------------------------------------------------------

++-ListN : ∀ {ds es} → ListN ds → ListN es → ListN (ds ++ es)
++-ListN {es = es} nilLN esL = prf
  where
    postulate prf : ListN ([] ++ es)
    {-# ATP prove prf #-}

++-ListN {es = es} (consLN {d} {ds} Nd LNds) LNes = prf $ ++-ListN LNds LNes
  where
    postulate prf : ListN (ds ++ es) →  -- IH.
                    ListN ((d ∷ ds) ++ es)
    {-# ATP prove prf #-}
