------------------------------------------------------------------------------
-- FOTC version of the domain predicate of a nested recursive function
-- given by the Bove-Capretta method
------------------------------------------------------------------------------

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. Vol. 2152 of LNCS. 2001

module Draft.FOTC.Program.Nest.DomainPredicate where

open import FOTC.Base

open import FOTC.Data.Nat

------------------------------------------------------------------------------

postulate
  nest   : D → D
  nest-0 :       nest zero     ≡ zero
  nest-S : ∀ d → nest (succ d) ≡ nest (nest d)

-- The nest function is total (non-terminating version).
-- nest-N : ∀ {n} → N n → N (nest n)
-- nest-N zN          = subst N (sym nest-0) zN
-- nest-N (sN {n} Nn) = subst N (sym (nest-S n)) (nest-N (nest-N Nn))

mutual
  -- The domain predicate of the nest function.
  data DomNest : (n : D) → N n → Set where
    dom0 : DomNest zero zN
    domS : ∀ {n} → (Nn : N n) →
                   (h₁ : DomNest n Nn) →
                   (h₂ : DomNest (nest n) (nest-N Nn h₁)) →
                   DomNest (succ n) (sN Nn)

  -- The nest function is total (via structural recursion in the
  -- domain predicate).
  nest-N : ∀ {n} → (Nn : N n) → DomNest n Nn → N (nest n)
  nest-N .zN dom0                     = subst N (sym nest-0) zN
  nest-N .(sN Nn) (domS {n} Nn h₁ h₂) =
    subst N (sym (nest-S n)) (nest-N (nest-N Nn h₁) h₂)
