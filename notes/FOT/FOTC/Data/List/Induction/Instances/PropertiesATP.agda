------------------------------------------------------------------------------
-- Properties related with lists
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

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
