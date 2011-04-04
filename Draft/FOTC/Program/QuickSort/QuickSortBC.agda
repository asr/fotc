------------------------------------------------------------------------------
-- Quicksort using the Bove-Capretta method
------------------------------------------------------------------------------

module QuickSortBC where

open import Data.Bool
open import Data.List -- hiding ( filter )
open import Data.Nat hiding (_≤_ ; _<_ ; _≥_ ; _>_)

------------------------------------------------------------------------------

_≤_ : ℕ → ℕ → Bool
zero  ≤ n     = true
suc m ≤ zero  = false
suc m ≤ suc n = m ≤ n

_<_ : ℕ → ℕ → Bool
m < n = suc m ≤ n

_≥_ : ℕ → ℕ → Bool
m ≥ n = n ≤ m

-- filter : {A : Set} → (A → Bool) → List A → List A
-- filter _ []    = []
-- filter P (x ∷ xs) with P x
-- ... | true  = x ∷ filter P xs
-- ... | false = filter P xs

-- Non-terminating quicksort.
qsNT : List ℕ → List ℕ
qsNT []       = []
qsNT (x ∷ xs) = qsNT (filter (λ y → y < x) xs) ++
                x ∷ qsNT (filter (λ y → x < y) xs)

-- Domain predicate for quicksort.
data Dqs : List ℕ → Set where
  dnil  : Dqs []
  dcons : ∀ {x xs} → Dqs (filter (λ y → y < x) xs) →
                     Dqs (filter (λ y → x < y) xs) →
                     Dqs (x ∷ xs)

-- Induction principle associated to the domain predicate of quicksort.
indDqs : (P : List ℕ → Set) →
         P [] →
         (∀ {x xs} → Dqs (filter (λ y → y < x) xs) →
                     P (filter (λ y → y < x) xs) →
                     Dqs (filter (λ y → x < y) xs) →
                     P (filter (λ y → x < y) xs) →
                     P (x ∷ xs)) →
         (∀ {xs} → Dqs xs → P xs)
indDqs P P[] Pcons dnil       = P[]
indDqs P P[] ih (dcons h₁ h₂) =
  ih h₁ (indDqs P P[] ih h₁) h₂ (indDqs P P[] ih h₂)

-- Quicksort algorithm by structural recursion on the domain predicate.
qsHelper : ∀ xs → Dqs xs → List ℕ
qsHelper .[]      dnil = []
qsHelper (x ∷ xs) (dcons h₁ h₂) =
  qsHelper (filter (λ y → y < x) xs) h₁ ++
  x ∷ qsHelper (filter (λ y → x < y) xs) h₂

-- The quicksort algorithm is total.
postulate
  allDqs : ∀ xs → Dqs xs

-- The quicksort algorithm.
qs : List ℕ → List ℕ
qs xs = qsHelper xs (allDqs xs)

l₁ : List ℕ
l₁ = []

l₂ = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []

l₃ = 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []

l₄ = 4 ∷ 1 ∷ 3 ∷ 5 ∷ 2 ∷ []
