------------------------------------------------------------------------------
-- Properties related with lists
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.List.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.Conat
open import Combined.FOTC.Data.List
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Congruence properties

postulate ++-leftCong : ∀ {xs ys zs} → xs ≡ ys → xs ++ zs ≡ ys ++ zs
{-# ATP prove ++-leftCong #-}

postulate mapCong₂ : ∀ {f xs ys} → xs ≡ ys → map f xs ≡ map f ys
{-# ATP prove mapCong₂ #-}

------------------------------------------------------------------------------
-- Totality properties

-- TODO (2019-06-09): Missing ATP proof.
postulate lengthList-N : ∀ {xs} → List xs → N (length xs)

++-List : ∀ {xs ys} → List xs → List ys → List (xs ++ ys)
++-List {ys = ys} lnil Lys = prf
  where postulate prf : List ([] ++ ys)
        {-# ATP prove prf #-}

++-List {ys = ys} (lcons x {xs} Lxs) Lys = prf (++-List Lxs Lys)
  where postulate prf : List (xs ++ ys) → List ((x ∷ xs) ++ ys)
        {-# ATP prove prf #-}

map-List : ∀ f {xs} → List xs → List (map f xs)
map-List f lnil = prf
  where postulate prf : List (map f [])
        {-# ATP prove prf #-}
map-List f (lcons x {xs} Lxs) = prf (map-List f Lxs)
  where postulate prf : List (map f xs) → List (map f (x ∷ xs))
        {-# ATP prove prf #-}

rev-List : ∀ {xs ys} → List xs → List ys → List (rev xs ys)
rev-List {ys = ys} lnil Lys = prf
  where postulate prf : List (rev [] ys)
        {-# ATP prove prf #-}
rev-List {ys = ys} (lcons x {xs} Lxs) Lys = prf (rev-List Lxs (lcons x Lys))
  where postulate prf : List (rev xs (x ∷ ys)) → List (rev (x ∷ xs) ys)
        {-# ATP prove prf #-}

postulate reverse-List : ∀ {xs} → List xs → List (reverse xs)
{-# ATP prove reverse-List rev-List #-}

-- Length properties

length-replicate : ∀ x {n} → N n → length (replicate n x) ≡ n
length-replicate x nzero = prf
  where postulate prf : length (replicate zero x) ≡ zero
        {-# ATP prove prf #-}
length-replicate x (nsucc {n} Nn) = prf (length-replicate x Nn)
  where postulate prf : length (replicate n x) ≡ n →
                        length (replicate (succ₁ n) x) ≡ succ₁ n
        {-# ATP prove prf #-}

postulate lg-xs≡∞→lg-x∷xs≡∞ : ∀ x xs → length xs ≡ ∞ → length (x ∷ xs) ≡ ∞
{-# ATP prove lg-xs≡∞→lg-x∷xs≡∞ #-}

-- TODO (2019-06-09): Missing ATP proof.
postulate lg-x<lg-x∷xs : ∀ x {xs} → List xs → length xs < length (x ∷ xs)

-- TODO (2019-06-09): Missing ATP proof.
postulate lg-xs<lg-[]→⊥ : ∀ {xs} → List xs → ¬ (length xs < length [])

-- Append properties

++-leftIdentity : ∀ xs → [] ++ xs ≡ xs
++-leftIdentity = ++-[]

++-rightIdentity : ∀ {xs} → List xs → xs ++ [] ≡ xs
++-rightIdentity lnil = prf
  where postulate prf : [] ++ [] ≡ []
        {-# ATP prove prf #-}

++-rightIdentity (lcons x {xs} Lxs) = prf (++-rightIdentity Lxs)
  where postulate prf : xs ++ [] ≡ xs → (x ∷ xs) ++ [] ≡ x ∷ xs
        {-# ATP prove prf #-}

++-assoc : ∀ {xs} → List xs → ∀ ys zs → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc .{[]} lnil ys zs = prf
  where postulate prf : ([] ++ ys) ++ zs ≡ [] ++ ys ++ zs
        {-# ATP prove prf #-}

++-assoc .{x ∷ xs} (lcons x {xs} Lxs) ys zs = prf (++-assoc Lxs ys zs)
  where postulate prf : (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs →
                        ((x ∷ xs) ++ ys) ++ zs ≡ (x ∷ xs) ++ ys ++ zs
        {-# ATP prove prf #-}

-- Map properties

map-++ : ∀ f {xs} → List xs → ∀ ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f lnil ys = prf
  where postulate prf : map f ([] ++ ys) ≡ map f [] ++ map f ys
        {-# ATP prove prf #-}

map-++ f (lcons x {xs} Lxs) ys = prf (map-++ f Lxs ys)
  where postulate prf : map f (xs ++ ys) ≡ map f xs ++ map f ys →
                        map f ((x ∷ xs) ++ ys) ≡ map f (x ∷ xs) ++ map f ys
        {-# ATP prove prf #-}

-- Reverse properties

postulate reverse-[x]≡[x] : ∀ x → reverse (x ∷ []) ≡ x ∷ []
{-# ATP prove reverse-[x]≡[x] #-}

rev-++ : ∀ {xs} → List xs → ∀ ys → rev xs ys ≡ rev xs [] ++ ys
rev-++ lnil ys = prf
  where postulate prf : rev [] ys ≡ rev [] [] ++ ys
        {-# ATP prove prf #-}
rev-++ (lcons x {xs} Lxs) ys = prf (rev-++ Lxs (x ∷ ys)) (rev-++ Lxs (x ∷ []))
  where postulate prf : rev xs (x ∷ ys) ≡ rev xs [] ++ x ∷ ys →
                        rev xs (x ∷ []) ≡ rev xs [] ++ x ∷ [] →
                        rev (x ∷ xs) ys ≡ rev (x ∷ xs) [] ++ ys
        {-# ATP prove prf ++-assoc rev-List #-}

reverse-++ : ∀ {xs ys} → List xs → List ys →
             reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ {ys = ys} lnil Lys = prf
  where postulate prf : reverse ([] ++ ys) ≡ reverse ys ++ reverse []
        {-# ATP prove prf ++-rightIdentity reverse-List #-}

reverse-++ (lcons x {xs} Lxs) lnil = prf
  where
  postulate prf : reverse ((x ∷ xs) ++ []) ≡ reverse [] ++ reverse (x ∷ xs)
  {-# ATP prove prf ++-rightIdentity #-}

reverse-++ (lcons x {xs} Lxs) (lcons y {ys} Lys) =
  prf (reverse-++ Lxs (lcons y Lys))
  where
  postulate prf : reverse (xs ++ y ∷ ys) ≡ reverse (y ∷ ys) ++
                                           reverse xs →
                  reverse ((x ∷ xs) ++ y ∷ ys) ≡ reverse (y ∷ ys) ++
                                                 reverse (x ∷ xs)
  {-# ATP prove prf reverse-List ++-List rev-++ ++-assoc #-}

reverse-∷ : ∀ x {ys} → List ys →
            reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])
reverse-∷ x lnil = prf
  where postulate prf : reverse (x ∷ []) ≡ reverse [] ++ x ∷ []
        {-# ATP prove prf #-}

reverse-∷ x (lcons y {ys} Lys) = prf
  where postulate prf : reverse (x ∷ y ∷ ys) ≡ reverse (y ∷ ys) ++ x ∷ []
        {-# ATP prove prf reverse-[x]≡[x] reverse-++ #-}

reverse-involutive : ∀ {xs} → List xs → reverse (reverse xs) ≡ xs
reverse-involutive lnil = prf
  where postulate prf : reverse (reverse []) ≡ []
        {-# ATP prove prf #-}

reverse-involutive (lcons x {xs} Lxs) = prf (reverse-involutive Lxs)
  where
  postulate prf : reverse (reverse xs) ≡ xs →
                  reverse (reverse (x ∷ xs)) ≡ x ∷ xs
  {-# ATP prove prf rev-List reverse-++ ++-List ++-rightIdentity #-}
