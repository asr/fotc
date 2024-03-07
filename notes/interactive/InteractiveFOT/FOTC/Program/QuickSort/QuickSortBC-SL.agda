------------------------------------------------------------------------------
-- Quicksort using the Bove-Capretta method
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --without-K      #-}

module InteractiveFOT.FOTC.Program.QuickSort.QuickSortBC-SL where

open import Data.List.Base
open import Data.Nat.Base
open import Data.Nat.Induction
open import Data.Nat.Properties

open import Induction
open import Induction.WellFounded

open import Level

open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module InvImg =
  Induction.WellFounded.Inverse-image {B = ℕ} {A = List ℕ} {_<_ = _<′_} length

------------------------------------------------------------------------------

-- Non-terminating quicksort.

{-# TERMINATING #-}
qsNT : List ℕ → List ℕ
qsNT []       = []
qsNT (x ∷ xs) = qsNT (filter (λ y → y ≤′? x) xs) ++
                x ∷ qsNT (filter (λ y → x ≤′? y) xs)

-- Domain predicate for quicksort.
data QSDom : List ℕ → Set where
  qsDom-[] : QSDom []
  qsDom-∷  : ∀ {x xs} →
             (QSDom (filter (λ y → y ≤′? x) xs)) →
             (QSDom (filter (λ y → x ≤′? y) xs)) →
             QSDom (x ∷ xs)

-- Induction principle associated to the domain predicate of quicksort.
-- (It was not necessary).
QSDom-ind : (P : List ℕ → Set) →
            P [] →
            (∀ {x xs} → QSDom (filter (λ y → y ≤′? x) xs) →
                        P (filter (λ y → y ≤′? x) xs) →
                        QSDom (filter (λ y → x ≤′? y) xs) →
                        P (filter (λ y → x ≤′? y) xs) →
                        P (x ∷ xs)) →
            (∀ {xs} → QSDom xs → P xs)
QSDom-ind P P[] ih qsDom-[]        = P[]
QSDom-ind P P[] ih (qsDom-∷ h₁ h₂) =
  ih h₁ (QSDom-ind P P[] ih h₁) h₂ (QSDom-ind P P[] ih h₂)

-- Well-founded relation on lists.
_⟪′_ : {A : Set} → List A → List A → Set
xs ⟪′ ys = length xs <′ length ys

wf-⟪′ : WellFounded _⟪′_
wf-⟪′ = InvImg.well-founded <′-wellFounded

-- The well-founded induction principle on _⟪′_.
-- postulate wfi-⟪′ : (P : List ℕ → Set) →
--                    (∀ xs → (∀ ys → ys ⟪′ xs → P ys) → P xs) →
--                    ∀ xs → P xs

-- The quicksort algorithm is total.

filter-length : {A : Set} {P : Pred A Level.zero} →
                (P? : Relation.Unary.Decidable P ) → ∀ xs → length (filter P? xs) ≤′ length xs
filter-length P? [] = ≤′-refl
filter-length P? (x ∷ xs) with P? x
... | yes _ = ≤⇒≤′ (s≤s (≤′⇒≤ (filter-length P? xs)))
... | no  _ = ≤′-step (filter-length P? xs)

module AllWF = Induction.WellFounded.All wf-⟪′

allQSDom : ∀ xs → QSDom xs
-- If we use wfi-⟪′ then allQSDom =  wfi-⟪′ P ih
allQSDom = build (AllWF.wfRec-builder _) P ih
  where
  P : List ℕ → Set
  P = QSDom

  -- If we use wfi-⟪′ then
  -- ih : ∀ zs → (∀ ys → ys ⟪′ zs → P ys) → P zs
  ih :  ∀ zs → WfRec _⟪′_ P zs → P zs
  ih []       h = qsDom-[]
  ih (z ∷ zs) h = qsDom-∷ prf₁ prf₂
    where
    c₁ : (y : ℕ) → Dec (y ≤′ z)
    c₁ y = y ≤′? z

    c₂ : (y : ℕ) → Dec (z ≤′ y)
    c₂ y = z ≤′? y

    f₁ : List ℕ
    f₁ = filter c₁ zs

    f₂ : List ℕ
    f₂ = filter c₂ zs

    prf₁ : QSDom (filter (λ y → y ≤′? z) zs)
    prf₁ = h {f₁} (≤⇒≤′ (s≤s (≤′⇒≤ (filter-length c₁ zs))))

    prf₂ : QSDom (filter (λ y → z ≤′? y) zs)
    prf₂ = h {f₂} (≤⇒≤′ (s≤s (≤′⇒≤ (filter-length c₂ zs))))

-- Quicksort algorithm by structural recursion on the domain predicate.
qsDom : ∀ xs → QSDom xs → List ℕ
qsDom .[]      qsDom-[]        = []
qsDom (x ∷ xs) (qsDom-∷ h₁ h₂) =
  qsDom (filter (λ y → y ≤′? x) xs) h₁ ++
  x ∷ qsDom (filter (λ y → x ≤′? y) xs) h₂

-- The quicksort algorithm.
qs : List ℕ → List ℕ
qs xs = qsDom xs (allQSDom xs)

-- Testing.
l₁ : List ℕ
l₁ = []
l₂ = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
l₃ = 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
l₄ = 4 ∷ 1 ∷ 3 ∷ 5 ∷ 2 ∷ []

t₁ : qs l₁ ≡ l₁
t₁ = refl

t₂ : qs l₂ ≡ l₂
t₂ = refl

t₃ : qs l₃ ≡ l₂
t₃ = refl

t₄ : qs l₄ ≡ l₂
t₄ = refl
