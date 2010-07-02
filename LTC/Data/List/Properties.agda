------------------------------------------------------------------------------
-- Properties related with lists
------------------------------------------------------------------------------

module LTC.Data.List.Properties where

open import LTC.Minimal
open import LTC.Data.Nat
open import LTC.Data.List

------------------------------------------------------------------------------

++-List : {ds es : D} → List ds → List es → List (ds ++ es)
++-List {es = es} nil esL = prf
  where
    postulate prf : List ([] ++ es)
    {-# ATP prove prf #-}

++-List {es = es} (cons d {ds} dsL) esL = prf (++-List dsL esL)
  where
    postulate prf : List (ds ++ es) →
                    List ((d ∷ ds) ++ es)
    {-# ATP prove prf cons #-}

++-leftIdentity : {ds : D} → List ds → [] ++ ds ≡ ds
++-leftIdentity {ds} _ = ++-[] ds

++-rightIdentity : {ds : D} → List ds → ds ++ [] ≡ ds
++-rightIdentity nil = prf
  where
    postulate prf : [] ++ [] ≡ []
    {-# ATP prove prf #-}

++-rightIdentity (cons d {ds} dsL) = prf (++-rightIdentity dsL)
  where
    postulate prf : ds ++ [] ≡ ds →
                    (d ∷ ds) ++ [] ≡ d ∷ ds
    {-# ATP prove prf #-}

-- -- Using the principle of induction on lists.
-- ++-assoc' : {as bs cs : D} → List as → List bs → List cs →
--             (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
-- ++-assoc' {as} {bs} {cs} asL bsL csL = indList P p[] iStep asL
--   where
--     P : D → Set
--     P = λ ds → (ds ++ bs) ++ cs ≡ ds ++ (bs ++ cs)

--     p[] : P []
--     p[] = prf
--       where
--         postulate prf : ([] ++ bs) ++ cs ≡ [] ++ bs ++ cs
--         {-# ATP prove prf #-}

--     iStep : (d : D){ds : D} → List ds →
--             (ds ++ bs) ++ cs ≡ ds ++ (bs ++ cs) →
--             ((d ∷ ds) ++ bs) ++ cs ≡ (d ∷ ds) ++ bs ++ cs
--     iStep d {ds} dsL Pds = prf
--       where
--         postulate prf : ((d ∷ ds) ++ bs) ++ cs ≡ (d ∷ ds) ++ bs ++ cs
--         {-# ATP prove prf #-}

++-assoc : {as bs cs : D} → List as → List bs → List cs →
           (as ++ bs) ++ cs ≡ as ++ (bs ++ cs)
++-assoc .{[]} {bs} {cs} nil bsL csL = prf
  where
    postulate prf : ([] ++ bs) ++ cs ≡ [] ++ bs ++ cs
    {-# ATP prove prf #-}

++-assoc .{d ∷ ds} {bs} {cs} (cons d {ds} dsL) bsL csL =
  prf (++-assoc dsL bsL csL)
  where
    postulate prf : (ds ++ bs) ++ cs ≡ ds ++ bs ++ cs →
                    ((d ∷ ds) ++ bs) ++ cs ≡ (d ∷ ds) ++ bs ++ cs
    {-# ATP prove prf #-}

reverse-List : {ds : D} → List ds → List (reverse ds)
reverse-List nil = prf
  where
    postulate prf : List (reverse [])
    {-# ATP prove prf nil #-}

reverse-List (cons d {ds} dsL) = prf (reverse-List dsL)
  where
    postulate prf : List (reverse ds) →
                    List (reverse (d ∷ ds))
    {-# ATP prove prf cons nil ++-List #-}

postulate
  reverse-[x]≡[x] : (d : D) → reverse (d ∷ []) ≡ d ∷ []
{-# ATP prove reverse-[x]≡[x] #-}

reverse-++ : {ds es : D} → List ds → List es →
             reverse (ds ++ es) ≡ reverse es ++ reverse ds
reverse-++ {es = es} nil esL = prf
  where
    postulate prf : reverse ([] ++ es) ≡ reverse es ++ reverse []
    {-# ATP prove prf ++-rightIdentity reverse-List #-}

reverse-++ {es = es} (cons d {ds} dsL) esL = prf (reverse-++ dsL esL)
  where
    postulate prf : reverse (ds ++ es) ≡ reverse es ++ reverse ds →
                    reverse ((d ∷ ds) ++ es) ≡ reverse es ++ reverse (d ∷ ds)
    {-# ATP prove prf ++-assoc nil cons reverse-List ++-List #-}

reverse² : {ds : D} → List ds → reverse (reverse ds) ≡ ds
reverse² nil = prf
  where
    postulate prf : reverse (reverse []) ≡ []
    {-# ATP prove prf #-}

reverse² (cons d {ds} dsL) = prf (reverse² dsL)
  where
    postulate prf : reverse (reverse ds) ≡ ds →
                    reverse (reverse (d ∷ ds)) ≡ d ∷ ds
    {-# ATP prove prf reverse-++ cons nil reverse-List ++-List #-}

map-++ : (f : D){ds es : D} → List ds → List es →
         map f (ds ++ es) ≡ map f ds ++ map f es
map-++ f {es = es} nil esL = prf
  where
    postulate prf : map f ([] ++ es) ≡ map f [] ++ map f es
    {-# ATP prove prf #-}
map-++ f {es = es} (cons d {ds} dsL) esL = prf (map-++ f dsL esL)
  where
    postulate prf : map f (ds ++ es) ≡ map f ds ++ map f es →
                    map f ((d ∷ ds) ++ es) ≡ map f (d ∷ ds) ++ map f es
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
