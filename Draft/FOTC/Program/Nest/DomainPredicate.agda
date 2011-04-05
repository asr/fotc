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

nest-≤ : ∀ {n} → N n → Dom n → LE (nest n) n
nest-≤ Nz dom0           =
  begin
    nest zero ≤ zero
      ≡⟨ subst (λ t → nest zero ≤ zero ≡ t ≤ zero)
               nest-0
               refl
      ⟩
    zero ≤ zero
      ≡⟨ x≤x zN ⟩
    true
  ∎

nest-≤ NSn (domS n h₁ h₂) =
  ≤-trans (nest-N (domS n h₁ h₂)) (nest-N h₁) NSn prf₁ prf₂
    where
      Nn : N n
      Nn = dom-N n h₁

      prf₁ : LE (nest (succ n)) (nest n)
      prf₁ =
        begin
          nest (succ n) ≤ nest n
            ≡⟨ subst (λ t → nest (succ n) ≤ nest n ≡ t ≤ nest n)
                     (nest-S n)
                     refl
            ⟩
          nest (nest n) ≤ nest n
            ≡⟨ nest-≤ (dom-N (nest n) h₂) h₂ ⟩
          true
          ∎

      prf₂ : LE (nest n) (succ n)
      prf₂ = ≤-trans (nest-N h₁) Nn NSn (nest-≤ Nn h₁) (x≤Sx Nn)

N→Dom : ∀ {n} → N n → Dom n
N→Dom = wfInd-LT P ih
  where
    P : D → Set
    P = Dom

    ih : ∀ {x} → N x → (∀ {y} → N y → LT y x → P y) → P x
    ih zN          h = dom0
    ih (sN {x} Nx) h =
      domS x dn-x (h (nest-N dn-x) (x≤y→x<Sy (nest-N dn-x) Nx (nest-≤ Nx dn-x)))
      where
        dn-x : Dom x
        dn-x = h Nx (x<Sx Nx)
