------------------------------------------------------------------------------
-- Well-founded induction on N
------------------------------------------------------------------------------

module LTC.Data.N.Induction.WellFounded where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Relation.Inequalities
open import LTC.Relation.Inequalities.Properties

------------------------------------------------------------------------------
-- Well-founded induction on N
-- Adapted from http://code.haskell.org/~dolio/agda-share/induction/.

wfIndN-LT :
   (P : D → Set) →
   ({m : D} → N m → ({n : D} → N n → LT n m → P n ) → P m ) →
   {n : D} → N n → P n
wfIndN-LT P accH Nn = accH Nn (wfAux Nn)
  where
    wfAux : {m : D} → N m → {n : D} → N n → LT n m → P n
    wfAux zN      Nn      n<0   = ⊥-elim (¬x<0 Nn n<0)
    wfAux (sN Nm) zN      0<Sm  = accH zN (λ Nn' n'<0 → ⊥-elim (¬x<0 Nn' n'<0))
    wfAux (sN {m} Nm) (sN {n} Nn) Sn<Sm =
      accH (sN Nn) (λ Nn' n'<Sn →
        wfAux Nm Nn' (Sx≤y→x<y Nn' Nm
                            (≤-trans (sN Nn') (sN Nn) Nm
                                     (x<y→Sx≤y Nn' (sN Nn) n'<Sn)
                                     (Sx≤Sy→x≤y {succ n} {m}
                                                (x<y→Sx≤y (sN Nn)
                                                          (sN Nm)
                                                          Sn<Sm)))))
