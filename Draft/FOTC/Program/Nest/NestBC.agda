------------------------------------------------------------------------------
-- Example of a nested recursive function using the Bove-Capretta
-- method
------------------------------------------------------------------------------

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. vol 2152 LNCS. 2001

module NestBC where

open import Data.Nat

------------------------------------------------------------------------------

postulate
  ≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
  x≤Sx    : ∀ n → n ≤ suc n
  wfIndℕ  : (P : ℕ → Set) →
            (∀ n → (∀ m → m < n → P m) → P n) →
            ∀ n → P n

mutual
  -- The domain predicate of the nest function.
  data DomNest : ℕ → Set where
    dom0 : DomNest 0
    domS : ∀ {n} → (h₁ : DomNest n) →
                   (h₂ : DomNest (nestD n h₁)) →
                   DomNest (suc n)

  -- The nest function by structural recursion on the domain predicate.
  nestD : ∀ n → DomNest n → ℕ
  nestD .0       dom0             = 0
  nestD .(suc n) (domS {n} h₁ h₂) = nestD (nestD n h₁) h₂

nestD-≤ : ∀ n → (h : DomNest n) → nestD n h ≤ n
nestD-≤ .0       dom0             = z≤n
nestD-≤ .(suc n) (domS {n} h₁ h₂) =
  ≤-trans (≤-trans (nestD-≤ (nestD n h₁) h₂) (nestD-≤ n h₁))
          (x≤Sx n)

-- The nest function is total.
allDomNest : ∀ n → DomNest n
allDomNest n = wfIndℕ DomNest ih n
  where
    P : ℕ → Set
    P = DomNest

    ih : (y : ℕ) → ((x : ℕ) → x < y → P x) → P y
    ih zero    _ = dom0
    ih (suc y) h = domS dn-y (h (nestD y dn-y) (s≤s (nestD-≤ y dn-y)))
       where
         helper : (x : ℕ) → x < y → P x
         helper x Sx≤y = h x (s≤s (≤-trans (x≤Sx x) Sx≤y))

         dn-y : DomNest y
         dn-y = ih y helper

-- The nest function.
nest : ℕ → ℕ
nest n = nestD n (allDomNest n)
