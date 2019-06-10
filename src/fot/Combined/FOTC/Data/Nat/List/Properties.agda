------------------------------------------------------------------------------
-- Properties related with lists of natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.Nat.List.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.Nat.List
open import Combined.FOTC.Data.List

------------------------------------------------------------------------------

++-ListN : ∀ {ms ns} → ListN ms → ListN ns → ListN (ms ++ ns)
++-ListN {ns = ns} lnnil nsL = prf
  where postulate prf : ListN ([] ++ ns)
        {-# ATP prove prf #-}

++-ListN {ns = ns} (lncons {m} {ms} Nd LNms) LNns = prf (++-ListN LNms LNns)
  where postulate prf : ListN (ms ++ ns) → ListN ((m ∷ ms) ++ ns)
        {-# ATP prove prf #-}
