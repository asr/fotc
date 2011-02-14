------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Induction.WellFoundedI where

open import LTC.Base

open import Common.Function

open import LTC.Data.Nat.Type

open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI

------------------------------------------------------------------------------
-- Well-founded induction on N.
-- Adapted from http://code.haskell.org/~dolio/agda-share/induction/.

wfInd-LT : (P : D → Set) →
           (∀ {m} → N m → (∀ {n} → N n → LT n m → P n) → P m) →
           ∀ {n} → N n → P n
wfInd-LT P accH Nn = accH Nn (helper Nn)
  where
    helper : ∀ {m n} → N m → N n → LT n m → P n
    helper zN      Nn n<0  = ⊥-elim $ x<0→⊥ Nn n<0
    helper (sN Nm) zN 0<Sm = accH zN (λ Nn' n'<0 → ⊥-elim $ x<0→⊥ Nn' n'<0)

    helper (sN {m} Nm) (sN {n} Nn) Sn<Sm = accH (sN Nn)
      (λ {n'} Nn' n'<Sn →
        let Sn'≤Sn : LE (succ n') (succ n)
            Sn'≤Sn = x<y→Sx≤y Nn' (sN Nn) n'<Sn

            Sn≤m : LE (succ n) m
            Sn≤m = Sx≤Sy→x≤y (x<y→Sx≤y (sN Nn) (sN Nm) Sn<Sm)

            Sn'≤m : LE (succ n') m
            Sn'≤m = ≤-trans (sN Nn') (sN Nn) Nm Sn'≤Sn Sn≤m

            n'<m : LT n' m
            n'<m = Sx≤y→x<y Nn' Nm Sn'≤m

        in  helper Nm Nn' n'<m
      )

-- Other version using different properties of inequalities.
wfInd-LT₁ :
   (P : D → Set) →
   (∀ {m} → N m → (∀ {n} → N n → LT n m → P n) → P m) →
   ∀ {n} → N n → P n
wfInd-LT₁ P accH Nn = accH Nn (helper Nn)
  where
    helper : ∀ {m n} → N m → N n → LT n m → P n
    helper zN     Nn n<0  = ⊥-elim $ x<0→⊥ Nn n<0
    helper (sN _) zN 0<Sm = accH zN (λ Nn' n'<0 → ⊥-elim $ x<0→⊥ Nn' n'<0)

    helper (sN {m} Nm) (sN {n} Nn) Sn<Sm = accH (sN Nn)
      (λ {n'} Nn' n'<Sn →
        let n<m : LT n m
            n<m = Sx<Sy→x<y Sn<Sm

            n'<m : LT n' m
            n'<m = [ (λ n'<n → <-trans Nn' Nn Nm n'<n n<m)
                   , (λ n'≡n → x≡y→y<z→x<z n'≡n n<m)
                   ] (x<Sy→x<y∨x≡y Nn' Nn n'<Sn)

        in  helper Nm Nn' n'<m
      )
