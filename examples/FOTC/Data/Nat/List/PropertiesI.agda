------------------------------------------------------------------------------
-- Properties related with lists of natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.List.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.List
open import FOTC.Data.List

------------------------------------------------------------------------------
-- See the ATP version.
postulate ++-ListN : ∀ {ms ns} → ListN ms → ListN ns → ListN (ms ++ ns)

map-ListN : ∀ f {ns} → (∀ {n} → N n → N (f · n)) → ListN ns → ListN (map f ns)
map-ListN f h nilLN                    = subst ListN (sym (map-[] f)) nilLN
map-ListN f h (consLN {n} {ns} Nn Lns) =
  subst ListN (sym (map-∷ f n ns)) (consLN (h Nn) (map-ListN f h Lns))
