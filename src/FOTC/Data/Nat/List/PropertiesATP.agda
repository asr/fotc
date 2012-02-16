------------------------------------------------------------------------------
-- Properties related with lists of natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.List.PropertiesATP where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.List

------------------------------------------------------------------------------

++-ListN : ∀ {ms ns} → ListN ms → ListN ns → ListN (ms ++ ns)
++-ListN {ns = ns} nilLN nsL = prf
  where
  postulate prf : ListN ([] ++ ns)
  {-# ATP prove prf #-}

++-ListN {ns = ns} (consLN {m} {ms} Nd LNms) LNns = prf $ ++-ListN LNms LNns
  where
  postulate prf : ListN (ms ++ ns) →  -- IH.
                  ListN ((m ∷ ms) ++ ns)
  {-# ATP prove prf #-}
