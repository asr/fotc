------------------------------------------------------------------------------
-- Properties related with lists of natural numbers
------------------------------------------------------------------------------

module LTC.Data.Nat.List.Properties where

open import LTC.Minimal

open import LTC.Data.Nat.List.Type using ( consLN ; ListN ; nilLN )
open import LTC.Data.List using ( [] ; _∷_ ; _++_ )

------------------------------------------------------------------------------

++-ListN : {ds es : D} → ListN ds → ListN es → ListN (ds ++ es)
++-ListN {es = es} nilLN esL = prf
  where
    postulate prf : ListN ([] ++ es)
    {-# ATP prove prf #-}

++-ListN {es = es} (consLN {d} {ds} Nd LNds) LNes = prf (++-ListN LNds LNes)
  where
    postulate prf : ListN (ds ++ es) →
                    ListN ((d ∷ ds) ++ es)
    {-# ATP prove prf #-}
