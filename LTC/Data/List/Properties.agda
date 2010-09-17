------------------------------------------------------------------------------
-- Properties related with lists
------------------------------------------------------------------------------

module LTC.Data.List.Properties where

open import LTC.Minimal

open import LTC.Data.Nat.Type using
  ( N ; sN ; zN -- The LTC natural numbers type
  )
open import LTC.Data.List using
  ( _++_ ; ++-[]
  ; List ; consL ; nilL -- The LTC list type
  ; length
  ; map
  ; replicate
  ; reverse
  )

------------------------------------------------------------------------------
-- Closure properties

++-List : {xs ys : D} → List xs → List ys → List (xs ++ ys)
++-List {ys = ys} nilL Lys = prf
  where
    postulate prf : List ([] ++ ys)
    {-# ATP prove prf #-}

++-List {ys = ys} (consL x {xs} Lxs) Lys = prf (++-List Lxs Lys)
  where
    postulate prf : List (xs ++ ys) →  -- IH.
                    List ((x ∷ xs) ++ ys)
    {-# ATP prove prf consL #-}

map-List : {xs : D}(f : D) → List xs → List (map f xs)
map-List f nilL = prf
  where
    postulate prf : List (map f [])
    {-# ATP prove prf nilL #-}
map-List f (consL x {xs} Lxs) = prf (map-List f Lxs)
  where
    postulate prf : List (map f xs) → -- IH.
                    List (map f (x ∷ xs))
    {-# ATP prove prf consL #-}

reverse-List : {xs : D} → List xs → List (reverse xs)
reverse-List nilL = prf
  where
    postulate prf : List (reverse [])
    {-# ATP prove prf nilL #-}

reverse-List (consL x {xs} Lxs) = prf (reverse-List Lxs)
  where
    postulate prf : List (reverse xs) →  -- IH.
                    List (reverse (x ∷ xs))
    {-# ATP prove prf consL nilL ++-List #-}

++-leftIdentity : {xs : D} → List xs → [] ++ xs ≡ xs
++-leftIdentity {xs} _ = ++-[] xs

++-rightIdentity : {xs : D} → List xs → xs ++ [] ≡ xs
++-rightIdentity nilL = prf
  where
    postulate prf : [] ++ [] ≡ []
    {-# ATP prove prf #-}

++-rightIdentity (consL x {xs} Lxs) = prf (++-rightIdentity Lxs)
  where
    postulate prf : xs ++ [] ≡ xs →  -- IH.
                    (x ∷ xs) ++ [] ≡ x ∷ xs
    {-# ATP prove prf #-}

++-assoc : {as bs cs : D} → List as → List bs → List cs →
           (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
++-assoc .{[]} {bs} {cs} nilL Lbs Lcs = prf
  where
    postulate prf : ([] ++ bs) ++ cs ≡ [] ++ bs ++ cs
    {-# ATP prove prf #-}

++-assoc .{x ∷ xs} {bs} {cs} (consL x {xs} Lxs) Lbs Lcs =
  prf (++-assoc Lxs Lbs Lcs)
  where
    postulate prf : (xs ++ bs) ++ cs ≡ xs ++ bs ++ cs →  -- IH.
                    ((x ∷ xs) ++ bs) ++ cs ≡ (x ∷ xs) ++ bs ++ cs
    {-# ATP prove prf #-}

postulate
  reverse-[x]≡[x] : (x : D) → reverse (x ∷ []) ≡ x ∷ []
{-# ATP prove reverse-[x]≡[x] #-}

reverse-++ : {xs ys : D} → List xs → List ys →
             reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ {ys = ys} nilL Lys = prf
  where
    postulate prf : reverse ([] ++ ys) ≡ reverse ys ++ reverse []
    {-# ATP prove prf ++-rightIdentity reverse-List #-}

reverse-++ {ys = ys} (consL x {xs} Lxs) Lys = prf (reverse-++ Lxs Lys)
  where
    postulate prf : reverse (xs ++ ys) ≡ reverse ys ++ reverse xs →  -- IH.
                    reverse ((x ∷ xs) ++ ys) ≡ reverse ys ++ reverse (x ∷ xs)
    -- E 1.2 no-success due to timeout (180).
    {-# ATP prove prf ++-assoc nilL consL reverse-List ++-List #-}

reverse² : {xs : D} → List xs → reverse (reverse xs) ≡ xs
reverse² nilL = prf
  where
    postulate prf : reverse (reverse []) ≡ []
    {-# ATP prove prf #-}

reverse² (consL x {xs} Lxs) = prf (reverse² Lxs)
  where
    postulate prf : reverse (reverse xs) ≡ xs →  -- IH.
                    reverse (reverse (x ∷ xs)) ≡ x ∷ xs
    {-# ATP prove prf reverse-++ consL nilL reverse-List ++-List #-}

map-++ : (f : D){xs ys : D} → List xs → List ys →
         map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f {ys = ys} nilL Lys = prf
  where
    postulate prf : map f ([] ++ ys) ≡ map f [] ++ map f ys
    {-# ATP prove prf #-}
map-++ f {ys = ys} (consL x {xs} Lxs) Lys = prf (map-++ f Lxs Lys)
  where
    postulate prf : map f (xs ++ ys) ≡ map f xs ++ map f ys →  -- IH.
                    map f ((x ∷ xs) ++ ys) ≡ map f (x ∷ xs) ++ map f ys
    -- E 1.2 no-success due to timeout (180).
    {-# ATP prove prf #-}

length-replicate : {n : D} → N n → (d : D) → length (replicate n d) ≡ n
length-replicate zN d = prf
  where
    postulate prf : length (replicate zero d) ≡ zero
    {-# ATP prove prf #-}
length-replicate (sN {n} Nn) d = prf (length-replicate Nn d)
  where
    postulate prf : length (replicate n d) ≡ n →  -- IH.
                    length (replicate (succ n) d) ≡ succ n
    {-# ATP prove prf #-}
