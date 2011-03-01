----------------------------------------------------------------------------
-- Well-founded induction on the natural numbers
----------------------------------------------------------------------------

open import FOTC.Base
open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.Inequalities

module FOTC.Data.Nat.Induction.Acc.WellFoundedInduction
  ( x<0→⊥        : ∀ {n} → N n → ¬ (LT n zero)
  ; Sx<Sy→x<y    : ∀ {m n} → LT (succ m) (succ n) → LT m n
  ; <-trans      : ∀ {m n o} → N m → N n → N o → LT m n → LT n o → LT m o
  ; x≡y→y<z→x<z  : ∀ {m n o} → m ≡ n → LT n o → LT m o
  ; x<Sy→x<y∨x≡y : ∀ {m n} → N m → N n → LT m (succ n) → LT m n ∨ m ≡ n
  ; x≤y→x<y∨x≡y  : ∀ {m n} → N m → N n → LE m n → LT m n ∨ m ≡ n
  ; x<Sy→x≤y     : ∀ {m n} → N m → N n → LT m (succ n) → LE m n
  )
  where

open import Common.Function

open import FOTC.Data.Nat.Induction.Acc.WellFounded

------------------------------------------------------------------------------
-- The relation LT is well-founded.
LT-wf : WellFounded LT
LT-wf Nn = acc Nn (helper Nn)
  where
    -- N.B. The helper function is the same that the function used by
    -- FOTC.Data.Nat.Induction.NonAcc.WellFoundedInductionATP.
    helper : ∀ {n m} → N n → N m → LT m n → Acc LT m
    helper zN     Nm m<0  = ⊥-elim $ x<0→⊥ Nm m<0
    helper (sN _) zN 0<Sn = acc zN (λ Nm' m'<0 → ⊥-elim $ x<0→⊥ Nm' m'<0)

    helper (sN {n} Nn) (sN {m} Nm) Sm<Sn = acc (sN Nm)
      (λ {m'} Nm' m'<Sm →
        let m<n : LT m n
            m<n = Sx<Sy→x<y Sm<Sn

            m'<n : LT m' n
            m'<n = [ (λ m'<m → <-trans Nm' Nm Nn m'<m m<n)
                   , (λ m'≡m → x≡y→y<z→x<z m'≡m m<n)
                   ] (x<Sy→x<y∨x≡y Nm' Nm m'<Sm)

        in  helper Nn Nm' m'<n
      )

-- A different proof that the relation LT is well-founded.
LT-wf₁ : WellFounded LT
LT-wf₁ zN      = acc zN (λ Nm m<0 → ⊥-elim (x<0→⊥ Nm m<0))
LT-wf₁ (sN Nn) = acc (sN Nn)
                     (λ Nm m<Sn → helper Nm Nn (LT-wf₁ Nn)
                                         (x<Sy→x≤y Nm Nn m<Sn))
  where
    helper : ∀ {n m} → N n → N m → Acc LT m → LE n m → Acc LT n
    helper {n} {m} Nn Nm (acc _ h) n≤m =
      [ (λ n<m → h Nn n<m)
      , (λ n≡m → helper₁ (sym n≡m) (acc Nm h))
      ] (x≤y→x<y∨x≡y Nn Nm n≤m)
      where
        helper₁ : ∀ {a b} → a ≡ b → Acc LT a → Acc LT b
        helper₁ refl acc-a = acc-a

-- Well-founded induction on the natural numbers.
wfInd-LT : (P : D → Set) →
           (∀ {m} → N m → (∀ {n} → N n → LT n m → P n) → P m) →
           ∀ {n} → N n → P n
wfInd-LT P = WellFoundedInduction LT-wf
