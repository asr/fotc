------------------------------------------------------------------------------
-- Properties related with lists
------------------------------------------------------------------------------

module LTC.Data.List.PropertiesATP where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC.Data.Nat.Type
  using ( N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC.Data.List
open import LTC.Data.List.Type

------------------------------------------------------------------------------
-- Closure properties

++-List : ∀ {xs ys} → List xs → List ys → List (xs ++ ys)
++-List {ys = ys} nilL Lys = prf
  where
    postulate prf : List ([] ++ ys)
    {-# ATP prove prf #-}

++-List {ys = ys} (consL x {xs} Lxs) Lys = prf $ ++-List Lxs Lys
  where
    postulate prf : List (xs ++ ys) →  -- IH.
                    List ((x ∷ xs) ++ ys)
    {-# ATP prove prf consL #-}

map-List : ∀ {xs} f → List xs → List (map f xs)
map-List f nilL = prf
  where
    postulate prf : List (map f [])
    {-# ATP prove prf nilL #-}
map-List f (consL x {xs} Lxs) = prf $ map-List f Lxs
  where
    postulate prf : List (map f xs) →  -- IH.
                    List (map f (x ∷ xs))
    {-# ATP prove prf consL #-}

rev-List : ∀ {xs ys} → List xs → List ys → List (rev xs ys)
rev-List {ys = ys} nilL Lys = prf
  where
    postulate prf : List (rev [] ys)
    {-# ATP prove prf nilL #-}
rev-List {ys = ys} (consL x {xs} Lxs) Lys = prf $ rev-List Lxs (consL x Lys)
  where
    postulate prf : List (rev xs (x ∷ ys)) →  -- IH.
                    List (rev (x ∷ xs) ys)
    {-# ATP prove prf #-}

reverse-List : ∀ {xs} → List xs → List (reverse xs)
reverse-List Lxs = rev-List Lxs nilL

++-leftIdentity : ∀ {xs} → List xs → [] ++ xs ≡ xs
++-leftIdentity {xs} _ = ++-[] xs

++-rightIdentity : ∀ {xs} → List xs → xs ++ [] ≡ xs
++-rightIdentity nilL = prf
  where
    postulate prf : [] ++ [] ≡ []
    {-# ATP prove prf #-}

++-rightIdentity (consL x {xs} Lxs) = prf $ ++-rightIdentity Lxs
  where
    postulate prf : xs ++ [] ≡ xs →  -- IH.
                    (x ∷ xs) ++ [] ≡ x ∷ xs
    {-# ATP prove prf #-}

++-assoc : ∀ {xs ys zs} → List xs → List ys → List zs →
           (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc .{[]} {ys} {zs} nilL Lys Lzs = prf
  where
    postulate prf : ([] ++ ys) ++ zs ≡ [] ++ ys ++ zs
    {-# ATP prove prf #-}

++-assoc .{x ∷ xs} {ys} {zs} (consL x {xs} Lxs) Lys Lzs =
  prf $ ++-assoc Lxs Lys Lzs
  where
    postulate prf : (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs →  -- IH.
                    ((x ∷ xs) ++ ys) ++ zs ≡ (x ∷ xs) ++ ys ++ zs
    {-# ATP prove prf #-}

-- N.B. This property does not depend of the type of lists.
postulate
  reverse-[x]≡[x] : ∀ x → reverse (x ∷ []) ≡ x ∷ []
{-# ATP prove reverse-[x]≡[x] #-}

rev-++-commute : ∀ {xs ys} → List xs → List ys → rev xs ys ≡ rev xs [] ++ ys
rev-++-commute {ys = ys} nilL Lys = prf
  where
    postulate prf : rev [] ys ≡ rev [] [] ++ ys
    {-# ATP prove prf #-}
rev-++-commute {ys = ys} (consL x {xs} Lxs) Lys =
  prf (rev-++-commute Lxs (consL x Lys)) (rev-++-commute Lxs (consL x nilL))
  where
    postulate prf : rev xs (x ∷ ys) ≡ rev xs [] ++ x ∷ ys →  -- IH.
                    rev xs (x ∷ []) ≡ rev xs [] ++ x ∷ [] →  -- IH.
                    rev (x ∷ xs) ys ≡ rev (x ∷ xs) [] ++ ys
    -- E 1.2: CPU time limit exceeded (180 sec).
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    -- Vampire 0.6 (revision 903): (Default) memory limit (timeout 180 sec).
    {-# ATP prove prf consL nilL ++-assoc rev-List ++-List #-}

reverse-∷ : ∀ x {ys} → List ys → reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])
reverse-∷ x nilL = prf
  where
    postulate prf : reverse (x ∷ []) ≡ reverse [] ++ x ∷ []
    {-# ATP prove prf #-}

reverse-∷ x (consL y {ys} Lys) = prf (reverse-∷ y Lys)
  where
    postulate prf : reverse (y ∷ ys) ≡ reverse ys ++ y ∷ [] → -- IH.
                    reverse (x ∷ y ∷ ys) ≡ reverse (y ∷ ys) ++ x ∷ []

reverse-++-commute : ∀ {xs ys} → List xs → List ys →
                     reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute {ys = ys} nilL Lys = prf
  where
    postulate prf : reverse ([] ++ ys) ≡ reverse ys ++ reverse []
    {-# ATP prove prf ++-rightIdentity reverse-List #-}

reverse-++-commute (consL x {xs} Lxs) nilL = prf
  where
    postulate prf : reverse ((x ∷ xs) ++ []) ≡ reverse [] ++ reverse (x ∷ xs)
    {-# ATP prove prf ++-rightIdentity reverse-List #-}
reverse-++-commute (consL x {xs} Lxs) (consL y {ys} Lys) =
  prf $ reverse-++-commute Lxs (consL y Lys)
  where
    postulate prf : reverse (xs ++ y ∷ ys) ≡ reverse (y ∷ ys) ++
                                             reverse xs →  -- IH.
                    reverse ((x ∷ xs) ++ y ∷ ys) ≡ reverse (y ∷ ys) ++
                                                   reverse (x ∷ xs)
    -- E 1.2: CPU time limit exceeded (180 sec).
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    -- Vampire 0.6 (revision 903): (Default) memory limit (using timeout 180 sec).
    {-# ATP prove prf consL nilL reverse-List ++-List rev-++-commute ++-assoc #-}

reverse² : ∀ {xs} → List xs → reverse (reverse xs) ≡ xs
reverse² nilL = prf
  where
    postulate prf : reverse (reverse []) ≡ []
    {-# ATP prove prf #-}

reverse² (consL x {xs} Lxs) = prf $ reverse² Lxs
  where
    postulate prf : reverse (reverse xs) ≡ xs →  -- IH.
                    reverse (reverse (x ∷ xs)) ≡ x ∷ xs
    -- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
    {-# ATP prove prf consL nilL rev-List rev-++-commute reverse-++-commute
                      ++-List ++-rightIdentity
    #-}

map-++-commute : ∀ f {xs ys} → List xs → List ys →
                 map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f {ys = ys} nilL Lys = prf
  where
    postulate prf : map f ([] ++ ys) ≡ map f [] ++ map f ys
    {-# ATP prove prf #-}
map-++-commute f {ys = ys} (consL x {xs} Lxs) Lys =
  prf $ map-++-commute f Lxs Lys
  where
    postulate prf : map f (xs ++ ys) ≡ map f xs ++ map f ys →  -- IH.
                    map f ((x ∷ xs) ++ ys) ≡ map f (x ∷ xs) ++ map f ys
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    {-# ATP prove prf #-}

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
