------------------------------------------------------------------------------
-- Quicksort using the Bove-Capretta method
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.QuickSort.QuickSortBC where

open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum

open import Induction
open import Induction.Nat
open import Induction.WellFounded

open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable

module InvImg =
  Induction.WellFounded.Inverse-image {A = List ℕ} {ℕ} {_<′_} length

------------------------------------------------------------------------------

_≤′?_ : Decidable _≤′_
m ≤′? n with m ≤? n
... | yes p = yes (≤⇒≤′ p)
... | no ¬p = no (λ m≤′n → ¬p (≤′⇒≤ m≤′n))

-- Non-terminating quicksort.

{-# NO_TERMINATION_CHECK #-}
qsNT : List ℕ → List ℕ
qsNT []       = []
qsNT (x ∷ xs) = qsNT (filter (λ y → ⌊ y ≤′? x ⌋) xs) ++
                x ∷ qsNT (filter (λ y → not ⌊ y ≤′? x ⌋) xs)

-- Domain predicate for quicksort.
data QSDom : List ℕ → Set where
  qsDom-[] : QSDom []
  qsDom-∷  : ∀ {x xs} →
             (QSDom (filter (λ y → ⌊ y ≤′? x ⌋) xs)) →
             (QSDom (filter (λ y → not ⌊ y ≤′? x ⌋) xs)) →
             QSDom (x ∷ xs)

-- Induction principle associated to the domain predicate of quicksort.
-- (It was not necessary).
indQSDom : (P : List ℕ → Set) →
           P [] →
           (∀ {x xs} → QSDom (filter (λ y → ⌊ y ≤′? x ⌋) xs) →
                       P (filter (λ y → ⌊ y ≤′? x ⌋) xs) →
                       QSDom (filter (λ y → not ⌊ y ≤′? x ⌋) xs) →
                       P (filter (λ y → not ⌊ y ≤′? x ⌋) xs) →
                       P (x ∷ xs)) →
           (∀ {xs} → QSDom xs → P xs)
indQSDom P P[] ih qsDom-[]        = P[]
indQSDom P P[] ih (qsDom-∷ h₁ h₂) =
  ih h₁ (indQSDom P P[] ih h₁) h₂ (indQSDom P P[] ih h₂)

-- Well-founded relation on lists.
_⟪′_ : {A : Set} → List A → List A → Set
xs ⟪′ ys = length xs <′ length ys

wf-⟪′ : Well-founded _⟪′_
wf-⟪′ = InvImg.well-founded <-well-founded

-- The well-founded induction principle on _⟪′_.
-- postulate
--   wfi-⟪′ : (P : List ℕ → Set) →
--            (∀ xs → (∀ ys → ys ⟪′ xs → P ys) → P xs) →
--            ∀ xs → P xs

-- The quicksort algorithm is total.

filter-length : {A : Set}(P : A → Bool) → ∀ xs →
                length (filter P xs) ≤′ length xs
filter-length P []       = ≤′-refl
filter-length P (x ∷ xs) with P x
... | true  = ≤⇒≤′ (s≤s (≤′⇒≤ (filter-length P xs)))
... | false = ≤′-step (filter-length P xs)

module AllWF = Induction.WellFounded.All wf-⟪′

allQSDom : ∀ xs → QSDom xs
-- If we use wfi-⟪′ then allQSDom =  wfi-⟪′ P ih
allQSDom = build AllWF.wfRec-builder P ih
  where
  P : List ℕ → Set
  P = QSDom

  -- If we use wfi-⟪′ then
  -- ih : ∀ zs → (∀ ys → ys ⟪′ zs → P ys) → P zs
  ih :  ∀ zs → WfRec _⟪′_ P zs → P zs
  ih []       h = qsDom-[]
  ih (z ∷ zs) h = qsDom-∷ prf₁ prf₂
    where
    c₁ : ℕ → Bool
    c₁ = λ y → ⌊ y ≤′? z ⌋

    c₂ : ℕ → Bool
    c₂ = λ y → not ⌊ y ≤′? z ⌋

    f₁ : List ℕ
    f₁ = filter c₁ zs

    f₂ : List ℕ
    f₂ = filter c₂ zs

    prf₁ : QSDom (filter (λ y → ⌊ y ≤′? z ⌋) zs)
    prf₁ = h f₁ (≤⇒≤′ (s≤s (≤′⇒≤ (filter-length c₁ zs))))

    prf₂ : QSDom (filter (λ y → not ⌊ y ≤′? z ⌋) zs)
    prf₂ = h f₂ (≤⇒≤′ (s≤s (≤′⇒≤ (filter-length c₂ zs))))

-- Quicksort algorithm by structural recursion on the domain predicate.
qsDom : ∀ xs → QSDom xs → List ℕ
qsDom .[]      qsDom-[]        = []
qsDom (x ∷ xs) (qsDom-∷ h₁ h₂) =
  qsDom (filter (λ y → ⌊ y ≤′? x ⌋) xs) h₁ ++
  x ∷ qsDom (filter (λ y → not ⌊ y ≤′? x ⌋) xs) h₂

-- The quicksort algorithm.
qs : List ℕ → List ℕ
qs xs = qsDom xs (allQSDom xs)

-- Testing.
l₁ : List ℕ
l₁ = []
l₂ = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
l₃ = 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
l₄ = 4 ∷ 1 ∷ 3 ∷ 5 ∷ 2 ∷ []

t₁ = qs l₁
t₂ = qs l₂
t₃ = qs l₃
t₄ = qs l₄
