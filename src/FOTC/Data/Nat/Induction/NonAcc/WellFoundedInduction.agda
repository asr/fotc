----------------------------------------------------------------------------
-- Well-founded induction on the natural numbers
----------------------------------------------------------------------------

module FOTC.Data.Nat.Induction.NonAcc.WellFoundedInduction where

open import FOTC.Base

open import Common.Function

open import FOTC.Data.Nat.Inequalities
-- open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers.
-- Adapted from http://code.haskell.org/~dolio/agda-share/induction/.
module WFInd₁
  ( x<0→⊥ : ∀ {n} → N n → ¬ (LT n zero)
  ; x<y→Sx≤y : ∀ {m n} → N m → N n → LT m n → LE (succ m) n
  ; ≤-trans : ∀ {m n o} → N m → N n → N o → LE m n → LE n o → LE m o
  ; Sx≤Sy→x≤y : ∀ {m n} → LE (succ m) (succ n) → LE m n
  ; Sx≤y→x<y : ∀ {m n} → N m → N n → LE (succ m) n → LT m n
  ) where

  wfInd-LT : (P : D → Set) →
             (∀ {n} → N n → (∀ {m} → N m → LT m n → P m) → P n) →
             ∀ {n} → N n → P n
  wfInd-LT P accH Nn = accH Nn (helper Nn)
    where
      helper : ∀ {n m} → N n → N m → LT m n → P m
      helper zN     Nm m<0  = ⊥-elim $ x<0→⊥ Nm m<0
      helper (sN _) zN 0<Sn = accH zN (λ Nm' m'<0 → ⊥-elim $ x<0→⊥ Nm' m'<0)

      helper (sN {n} Nn) (sN {m} Nm) Sm<Sn = accH (sN Nm)
        (λ {m'} Nm' m'<Sm →
          let Sm'≤Sm : LE (succ m') (succ m)
              Sm'≤Sm = x<y→Sx≤y Nm' (sN Nm) m'<Sm

              Sm≤n : LE (succ m) n
              Sm≤n = Sx≤Sy→x≤y (x<y→Sx≤y (sN Nm) (sN Nn) Sm<Sn)

              Sm'≤n : LE (succ m') n
              Sm'≤n = ≤-trans (sN Nm') (sN Nm) Nn Sm'≤Sm Sm≤n

              m'<n : LT m' n
              m'<n = Sx≤y→x<y Nm' Nn Sm'≤n

          in  helper Nn Nm' m'<n
        )

------------------------------------------------------------------------------
-- Other version of well-founded induction on the natural numbers
-- using different properties of inequalities.
module WFInd₂
  ( x<0→⊥ : ∀ {n} → N n → ¬ (LT n zero)
  ; Sx<Sy→x<y : ∀ {m n} → LT (succ m) (succ n) → LT m n
  ; <-trans : ∀ {m n o} → N m → N n → N o → LT m n → LT n o → LT m o
  ; x≡y→y<z→x<z : ∀ {m n o} → m ≡ n → LT n o → LT m o
  ; x<Sy→x<y∨x≡y : ∀ {m n} → N m → N n → LT m (succ n) → LT m n ∨ m ≡ n
  ) where

  wfInd-LT : (P : D → Set) →
             (∀ {n} → N n → (∀ {m} → N m → LT m n → P m) → P n) →
             ∀ {n} → N n → P n
  wfInd-LT P accH Nn = accH Nn (helper Nn)
    where
      helper : ∀ {n m} → N n → N m → LT m n → P m
      helper zN     Nm m<0  = ⊥-elim $ x<0→⊥ Nm m<0
      helper (sN _) zN 0<Sn = accH zN (λ Nm' m'<0 → ⊥-elim $ x<0→⊥ Nm' m'<0)

      helper (sN {n} Nn) (sN {m} Nm) Sm<Sn = accH (sN Nm)
        (λ {m'} Nm' m'<Sm →
          let m<n : LT m n
              m<n = Sx<Sy→x<y Sm<Sn

              m'<n : LT m' n
              m'<n = [ (λ m'<m → <-trans Nm' Nm Nn m'<m m<n)
                     , (λ m'≡m → x≡y→y<z→x<z m'≡m m<n)
                     ] (x<Sy→x<y∨x≡y Nm' Nm m'<Sm)

          in  helper Nn Nm' m'<n
        )
