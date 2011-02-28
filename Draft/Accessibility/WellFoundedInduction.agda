----------------------------------------------------------------------------
-- Well-founded induction on the relation LT using the accessibility
-- relation
----------------------------------------------------------------------------


module Draft.Accessibility.WellFoundedInduction where

open import FOTC.Base

open import Common.Function

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Induction.WellFounded
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI

----------------------------------------------------------------------------

-- The LT relation is well-founded.
LT-wf : WellFounded LT
LT-wf Nn = acc Nn (helper Nn)

  where
    helper : ∀ {m n} → N m → N n → LT n m → Acc LT n
    helper zN     Nn n<0  = ⊥-elim $ x<0→⊥ Nn n<0
    helper (sN _) zN 0<Sm = acc zN (λ Nn' n'<0 → ⊥-elim $ x<0→⊥ Nn' n'<0)

    helper (sN {m} Nm) (sN {n} Nn) Sn<Sm = acc (sN Nn)
      (λ {n'} Nn' n'<Sn →
        let n<m : LT n m
            n<m = Sx<Sy→x<y Sn<Sm

            n'<m : LT n' m
            n'<m = [ (λ n'<n → <-trans Nn' Nn Nm n'<n n<m)
                   , (λ n'≡n → x≡y→y<z→x<z n'≡n n<m)
                   ] (x<Sy→x<y∨x≡y Nn' Nn n'<Sn)

        in  helper Nm Nn' n'<m
      )

-- Well-founded induction on the relation LT.
wfInd-LT : (P : D → Set) →
           (∀ {m} → N m → (∀ {n} → N n → LT n m → P n) → P m) →
           ∀ {n} → N n → P n
wfInd-LT P = WellFoundedInduction LT-wf
