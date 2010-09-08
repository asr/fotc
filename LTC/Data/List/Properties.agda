------------------------------------------------------------------------------
-- Properties related with lists
------------------------------------------------------------------------------

module LTC.Data.List.Properties where

open import LTC.Minimal

open import LTC.Data.Nat.Type using ( N ; sN ; zN )
open import LTC.Data.List using
  ( [] ; _∷_
  ; _++_ ; ++-[]
  ; List ; consL ; nilL
  ; length
  ; map
  ; replicate
  ; reverse
  )

------------------------------------------------------------------------------

++-List : {ds es : D} → List ds → List es → List (ds ++ es)
++-List {es = es} nilL esL = prf
  where
    postulate prf : List ([] ++ es)
    {-# ATP prove prf #-}

++-List {es = es} (consL d {ds} Lds) esL = prf (++-List Lds esL)
  where
    postulate prf : List (ds ++ es) →
                    List ((d ∷ ds) ++ es)
    {-# ATP prove prf consL #-}

++-leftIdentity : {ds : D} → List ds → [] ++ ds ≡ ds
++-leftIdentity {ds} _ = ++-[] ds

++-rightIdentity : {ds : D} → List ds → ds ++ [] ≡ ds
++-rightIdentity nilL = prf
  where
    postulate prf : [] ++ [] ≡ []
    {-# ATP prove prf #-}

++-rightIdentity (consL d {ds} Lds) = prf (++-rightIdentity Lds)
  where
    postulate prf : ds ++ [] ≡ ds →
                    (d ∷ ds) ++ [] ≡ d ∷ ds
    {-# ATP prove prf #-}

++-assoc : {as bs cs : D} → List as → List bs → List cs →
           (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
++-assoc .{[]} {bs} {cs} nilL bsL csL = prf
  where
    postulate prf : ([] ++ bs) ++ cs ≡ [] ++ bs ++ cs
    {-# ATP prove prf #-}

++-assoc .{d ∷ ds} {bs} {cs} (consL d {ds} Lds) bsL csL =
  prf (++-assoc Lds bsL csL)
  where
    postulate prf : (ds ++ bs) ++ cs ≡ ds ++ bs ++ cs →
                    ((d ∷ ds) ++ bs) ++ cs ≡ (d ∷ ds) ++ bs ++ cs
    {-# ATP prove prf #-}

reverse-List : {ds : D} → List ds → List (reverse ds)
reverse-List nilL = prf
  where
    postulate prf : List (reverse [])
    {-# ATP prove prf nilL #-}

reverse-List (consL d {ds} Lds) = prf (reverse-List Lds)
  where
    postulate prf : List (reverse ds) →
                    List (reverse (d ∷ ds))
    {-# ATP prove prf consL nilL ++-List #-}

postulate
  reverse-[x]≡[x] : (d : D) → reverse (d ∷ []) ≡ d ∷ []
{-# ATP prove reverse-[x]≡[x] #-}

reverse-++ : {ds es : D} → List ds → List es →
             reverse (ds ++ es) ≡ reverse es ++ reverse ds
reverse-++ {es = es} nilL esL = prf
  where
    postulate prf : reverse ([] ++ es) ≡ reverse es ++ reverse []
    {-# ATP prove prf ++-rightIdentity reverse-List #-}

reverse-++ {es = es} (consL d {ds} Lds) esL = prf (reverse-++ Lds esL)
  where
    postulate prf : reverse (ds ++ es) ≡ reverse es ++ reverse ds →
                    reverse ((d ∷ ds) ++ es) ≡ reverse es ++ reverse (d ∷ ds)
    -- E 1.2 cannot prove this postulate with --time=180.
    {-# ATP prove prf ++-assoc nilL consL reverse-List ++-List #-}

reverse² : {ds : D} → List ds → reverse (reverse ds) ≡ ds
reverse² nilL = prf
  where
    postulate prf : reverse (reverse []) ≡ []
    {-# ATP prove prf #-}

reverse² (consL d {ds} Lds) = prf (reverse² Lds)
  where
    postulate prf : reverse (reverse ds) ≡ ds →
                    reverse (reverse (d ∷ ds)) ≡ d ∷ ds
    {-# ATP prove prf reverse-++ consL nilL reverse-List ++-List #-}

map-++ : (f : D){ds es : D} → List ds → List es →
         map f (ds ++ es) ≡ map f ds ++ map f es
map-++ f {es = es} nilL esL = prf
  where
    postulate prf : map f ([] ++ es) ≡ map f [] ++ map f es
    {-# ATP prove prf #-}
map-++ f {es = es} (consL d {ds} Lds) esL = prf (map-++ f Lds esL)
  where
    postulate prf : map f (ds ++ es) ≡ map f ds ++ map f es →
                    map f ((d ∷ ds) ++ es) ≡ map f (d ∷ ds) ++ map f es
    -- E 1.2 cannot prove this postulate with --time=180.
    {-# ATP prove prf #-}

length-replicate : {n : D} → N n → (d : D) → length (replicate n d) ≡ n
length-replicate zN d = prf
  where
    postulate prf : length (replicate zero d) ≡ zero
    {-# ATP prove prf #-}
length-replicate (sN {n} Nn) d = prf (length-replicate Nn d)
  where
    postulate prf : length (replicate n d) ≡ n →
                    length (replicate (succ n) d) ≡ succ n
    {-# ATP prove prf #-}
