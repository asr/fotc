------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Induction.Acc.WellFoundedInductionI where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.Type
open import FOTC.Induction.WellFounded

------------------------------------------------------------------------------
-- The relation LT is well-founded.
module WF-LT where
  wf-LT : WellFounded LT
  wf-LT Nn = acc (helper Nn)
    where
    -- N.B. The helper function is the same that the function used by
    -- FOTC.Data.Nat.Induction.NonAcc.WellFoundedInductionATP.
    helper : ∀ {n m} → N n → N m → LT m n → Acc N LT m
    helper zN     Nm m<0  = ⊥-elim $ x<0→⊥ Nm m<0
    helper (sN _) zN 0<Sn = acc (λ Nm' m'<0 → ⊥-elim $ x<0→⊥ Nm' m'<0)

    helper (sN {n} Nn) (sN {m} Nm) Sm<Sn =
      acc (λ {m'} Nm' m'<Sm →
             let m<n : LT m n
                 m<n = Sx<Sy→x<y Sm<Sn

                 m'<n : LT m' n
                 m'<n = [ (λ m'<m → <-trans Nm' Nm Nn m'<m m<n)
                        , (λ m'≡m → x≡y→y<z→x<z m'≡m m<n)
                        ] (x<Sy→x<y∨x≡y Nm' Nm m'<Sm)

             in  helper Nn Nm' m'<n
          )

  -- Well-founded induction on the natural numbers.
  wfInd-LT : (P : D → Set) →
             (∀ {n} → N n → (∀ {m} → N m → LT m n → P m) → P n) →
             ∀ {n} → N n → P n
  wfInd-LT P = WellFoundedInduction wf-LT

------------------------------------------------------------------------------
-- The relation LT is well-founded (a different proof).
module WF₁-LT where

  wf-LT : WellFounded {N} LT
  wf-LT zN      = acc (λ Nm m<0 → ⊥-elim (x<0→⊥ Nm m<0))
  wf-LT (sN Nn) = acc (λ Nm m<Sn → helper Nm Nn (wf-LT Nn)
                                          (x<Sy→x≤y Nm Nn m<Sn))
    where
    helper : ∀ {n m} → N n → N m → Acc N LT m → LE n m → Acc N LT n
    helper {n} {m} Nn Nm (acc h) n≤m =
      [ (λ n<m → h Nn n<m)
      , (λ n≡m → helper₁ (sym n≡m) (acc h))
      ] (x≤y→x<y∨x≡y Nn Nm n≤m)
      where
      helper₁ : ∀ {a b} → a ≡ b → Acc N LT a → Acc N LT b
      helper₁ a≡b acc-a = subst (Acc N LT) a≡b acc-a
