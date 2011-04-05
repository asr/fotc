------------------------------------------------------------------------------
-- FOTC version of the domain predicate of a nested recursive function
-- given by the Bove-Capretta method
------------------------------------------------------------------------------

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. Vol. 2152 of LNCS. 2001

module Draft.FOTC.Program.Nest.DomainPredicate where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

postulate
  nest   : D → D
  nest-0 :       nest zero     ≡ zero
  nest-S : ∀ d → nest (succ d) ≡ nest (nest d)

-- The nest function is total (non-terminating version).
-- nest-N : ∀ {n} → N n → N (nest n)
-- nest-N zN          = subst N (sym nest-0) zN
-- nest-N (sN {n} Nn) = subst N (sym (nest-S n)) (nest-N (nest-N Nn))

data Dom : D → Set where
  dom0 :                              Dom zero
  domS : ∀ d → Dom d → Dom (nest d) → Dom (succ d)

-- The domain predicate is total.
dom-N : ∀ d → Dom d → N d
dom-N .zero     dom0           = zN
dom-N .(succ d) (domS d h₁ h₂) = sN (dom-N d h₁)

-- The nest function is total in its domain (via structural recursion
-- in the domain predicate).
nest-N : ∀ {d} → Dom d → N (nest d)
nest-N dom0           = subst N (sym nest-0) zN
nest-N (domS d h₁ h₂) = subst N (sym (nest-S d)) (nest-N h₂)

postulate
  nest-≤ : ∀ {n} → N n → LE (nest n) n

N→Dom : ∀ {n} → N n → Dom n
N→Dom = wfInd-LT P ih
  where
    P : D → Set
    P = Dom

    ih : ∀ {x} → N x → (∀ {y} → N y → LT y x → P y) → P x
    ih zN          h = dom0
    ih (sN {x} Nx) h = domS x dn-x (h (nest-N dn-x)
                                      (x≤y→x<Sy (nest-N dn-x) Nx (nest-≤ Nx)))
      where
        dn-x : Dom x
        dn-x = h Nx (x<Sx Nx)
