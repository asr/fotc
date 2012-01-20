----------------------------------------------------------------------------
-- Well-founded induction on the natural numbers
----------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInductionI where

open import Common.Function

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.EliminationProperties
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI
open import LTC-PCF.Data.Nat.Type

------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers.
-- Adapted from http://code.haskell.org/~dolio/agda-share/induction/.

module WFInd where

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
        let Sm'≤Sm : LE (succ₁ m') (succ₁ m)
            Sm'≤Sm = x<y→Sx≤y Nm' (sN Nm) m'<Sm

            Sm≤n : LE (succ₁ m) n
            Sm≤n = Sx≤Sy→x≤y (x<y→Sx≤y (sN Nm) (sN Nn) Sm<Sn)

            Sm'≤n : LE (succ₁ m') n
            Sm'≤n = ≤-trans (sN Nm') (sN Nm) Nn Sm'≤Sm Sm≤n

            m'<n : LT m' n
            m'<n = Sx≤y→x<y Nm' Nn Sm'≤n

        in  helper Nn Nm' m'<n
      )

------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers (using different
-- properties of inequalities).

module WFInd₁ where

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
