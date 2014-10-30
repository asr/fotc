------------------------------------------------------------------------------
-- Properties related with lists using instances of the induction principle
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Data.List.Induction.Instances.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Totality properties

lengthList-N-ind-instance :
  N (length []) →
  (∀ x {xs} → N (length xs) → N (length (x ∷ xs))) →
  ∀ {xs} → List xs → N (length xs)
lengthList-N-ind-instance = List-ind (λ as → N (length as))

postulate lengthList-N : ∀ {xs} → List xs → N (length xs)
{-# ATP prove lengthList-N lengthList-N-ind-instance #-}

++-List-ind-instance :
  ∀ {ys} →
  List ([] ++ ys) →
  (∀ x {xs} → List (xs ++ ys) → List ((x ∷ xs) ++ ys)) →
  ∀ {xs} → List xs → List (xs ++ ys)
++-List-ind-instance {ys} = List-ind (λ as → List (as ++ ys))

postulate ++-List : ∀ {xs ys} → List xs → List ys → List (xs ++ ys)
{-# ATP prove ++-List ++-List-ind-instance #-}

map-List-ind-instance :
  ∀ {f} →
  List (map f []) →
  (∀ x {xs} → List (map f xs) → List (map f (x ∷ xs))) →
  ∀ {xs} → List xs → List (map f xs)
map-List-ind-instance {f} = List-ind (λ as → List (map f as))

postulate map-List : ∀ f {xs} → List xs → List (map f xs)
{-# ATP prove map-List map-List-ind-instance #-}

------------------------------------------------------------------------------

++-assoc-ind-instance :
  ∀ {ys zs} →
  ([] ++ ys) ++ zs ≡ [] ++ ys ++ zs →
  (∀ x {xs} →
    (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs →
    ((x ∷ xs) ++ ys) ++ zs ≡ (x ∷ xs) ++ ys ++ zs) →
  ∀ {xs} → List xs → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc-ind-instance {ys} {zs} =
  List-ind (λ as → (as ++ ys) ++ zs ≡ as ++ ys ++ zs )

postulate
  ++-assoc : ∀ {xs} → List xs → ∀ ys zs → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
{-# ATP prove ++-assoc ++-assoc-ind-instance #-}

map-++-ind-instance :
  ∀ {f} {ys} →
  map f ([] ++ ys) ≡ map f [] ++ map f ys →
  (∀ x {xs} → map f (xs ++ ys) ≡ map f xs ++ map f ys →
    map f ((x ∷ xs) ++ ys) ≡ map f (x ∷ xs) ++ map f ys) →
  ∀ {xs} → List xs → map f (xs ++ ys) ‌≡ map f xs ++ map f ys
map-++-ind-instance {f} {ys} =
  List-ind (λ as → map f (as ++ ys) ≡ map f as ++ map f ys)

postulate
  map-++ : ∀ f {xs} → List xs → ∀ ys →
           map f (xs ++ ys) ≡ map f xs ++ map f ys
{-# ATP prove map-++ map-++-ind-instance #-}
