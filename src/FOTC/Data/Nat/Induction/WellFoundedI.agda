----------------------------------------------------------------------------
-- Well-founded induction on the natural numbers
----------------------------------------------------------------------------

module FOTC.Data.Nat.Induction.WellFoundedI where

open import FOTC.Base

open import Common.Function

open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Well-founded induction on N.
-- Adapted from http://code.haskell.org/~dolio/agda-share/induction/.

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

-- Other version using different properties of inequalities.
wfInd-LT₁ : (P : D → Set) →
            (∀ {n} → N n → (∀ {m} → N m → LT m n → P m) → P n) →
            ∀ {n} → N n → P n
wfInd-LT₁ P accH Nn = accH Nn (helper Nn)
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
