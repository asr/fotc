------------------------------------------------------------------------------
-- Properties related with lists of natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.Nat.List.Properties where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.List
open import Interactive.FOTC.Data.List

------------------------------------------------------------------------------
-- See the ATP version.
postulate ++-ListN : ∀ {ms ns} → ListN ms → ListN ns → ListN (ms ++ ns)

map-ListN : ∀ f {ns} → (∀ {n} → N n → N (f · n)) → ListN ns → ListN (map f ns)
map-ListN f h lnnil                    = subst ListN (sym (map-[] f)) lnnil
map-ListN f h (lncons {n} {ns} Nn Lns) =
  subst ListN (sym (map-∷ f n ns)) (lncons (h Nn) (map-ListN f h Lns))
