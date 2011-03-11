------------------------------------------------------------------------------
-- Properties related with the length of lists
------------------------------------------------------------------------------

module FOTC.Data.List.Length.PropertiesATP where

open import FOTC.Base

open import Common.Function

open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Type
open import FOTC.Data.List
open import FOTC.Data.List.Type

------------------------------------------------------------------------------

length-N : ∀ {xs} → List xs → N (length xs)
length-N nilL               = subst N (sym length-[]) zN
length-N (consL x {xs} Lxs) = subst N (sym (length-∷ x xs)) (sN (length-N Lxs))

length-replicate : ∀ d {n} → N n → length (replicate n d) ≡ n
length-replicate d zN = prf
  where
    postulate prf : length (replicate zero d) ≡ zero
    {-# ATP prove prf #-}
length-replicate d (sN {n} Nn) = prf $ length-replicate d Nn
  where
    postulate prf : length (replicate n d) ≡ n →  -- IH.
                    length (replicate (succ n) d) ≡ succ n
    {-# ATP prove prf #-}

lg-x<lg-x∷xs : ∀ x {xs} → List xs → LT (length xs) (length (x ∷ xs))
lg-x<lg-x∷xs x nilL = prf
  where
    postulate prf : LT (length []) (length (x ∷ []))
    {-# ATP prove prf #-}

lg-x<lg-x∷xs x (consL y {xs} Lxs) = prf (lg-x<lg-x∷xs y Lxs)
  where
    postulate prf : LT (length xs) (length (y ∷ xs)) →  -- IH.
                    LT (length (y ∷ xs)) (length (x ∷ y ∷ xs))
