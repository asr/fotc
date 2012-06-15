------------------------------------------------------------------------------
-- FOTC version of the domain predicate of quicksort given by the
-- Bove-Capretta method
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.QuickSort.DomainPredicate where

open import FOTC.Base
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.Type
open import FOTC.Data.List

------------------------------------------------------------------------------

-- We need to define monadic inequalities.
postulate
  le gt : D

  le-00 :         le · zero    · zero    ≡ false
  le-0S : ∀ d →   le · zero    · succ₁ d ≡ true
  le-S0 : ∀ d →   le · succ₁ d · zero    ≡ false
  le-SS : ∀ d e → le · succ₁ d · succ₁ e ≡ d < e

postulate
  filter    : D → D → D
  filter-[] : ∀ f →      filter f []       ≡ []
  filter-∷  : ∀ f d ds → filter f (d ∷ ds) ≡
                if f · d then d ∷ filter f (d ∷ ds) else filter f (d ∷ ds)

postulate
  filter-List : ∀ f {xs} → List xs → List (filter f xs)

postulate
  qs    : D → D
  qs-[] : qs [] ≡ []
  qs-∷  : ∀ x xs → qs (x ∷ xs) ≡ qs (filter (gt · x) xs) ++
                                 x ∷ qs (filter (le · x) xs)

-- Domain predicate for quicksort.
data Dqs : {xs : D} → List xs → Set where
  dnil  : Dqs nilL
  dcons : ∀ {x xs} → (Lxs : List xs) →
                     Dqs (filter-List (gt · x) Lxs) →
                     Dqs (filter-List (le · x) Lxs) →
                     Dqs (consL x Lxs)

-- Induction principle associated to the domain predicate of quicksort.
indDqs : (P : {xs : D} → List xs → Set) →
         P nilL →
         (∀ {x xs} → (Lxs : List xs) →
                     Dqs (filter-List (gt · x) Lxs) →
                     P (filter-List (gt · x) Lxs) →
                     Dqs (filter-List (le · x) Lxs) →
                     P (filter-List (le · x) Lxs) →
                     P (consL x Lxs)) →
         (∀ {xs} → {Lxs : List xs} → Dqs Lxs → P Lxs)
indDqs P P[] ih dnil              = P[]
indDqs P P[] ih (dcons Lxs h₁ h₂) =
  ih Lxs h₁ (indDqs P P[] ih h₁) h₂ (indDqs P P[] ih h₂)
