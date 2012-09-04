------------------------------------------------------------------------------
-- Properties related with lists of natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.List.PropertiesATP where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Nat.List
open import FOTC.Data.List

------------------------------------------------------------------------------

++-ListN : ∀ {ms ns} → ListN ms → ListN ns → ListN (ms ++ ns)
++-ListN {ns = ns} lnnil nsL = prf
  where postulate prf : ListN ([] ++ ns)
        {-# ATP prove prf #-}

++-ListN {ns = ns} (lncons {m} {ms} Nd LNms) LNns = prf $ ++-ListN LNms LNns
  where postulate prf : ListN (ms ++ ns) → ListN ((m ∷ ms) ++ ns)
        {-# ATP prove prf #-}
