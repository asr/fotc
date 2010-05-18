------------------------------------------------------------------------------
-- Well-founded induction on N
------------------------------------------------------------------------------

module LTC.Data.N.Induction.WellFounded where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Relation.Inequalities
open import LTC.Relation.Inequalities.Properties

open import Postulates using ( Sx≤Sy→x≤y ; ≤-trans )

------------------------------------------------------------------------------
-- General setting.
-- Adapted from http://www.iis.sinica.edu.tw/~scm/2008/well-founded-recursion-and-accessibility/.

data AccN (R : D → D → Set) : {x : D} → N x → Set where
  accN : {x : D} → (Nx : N x) → ({y : D} → (Ny : N y) → R y x → AccN R Ny) →
         AccN R Nx

WellFoundedN : (D → D → Set) → Set
WellFoundedN R = {x : D} → (Nx : N x) → AccN R Nx

accFoldN : (R : D → D → Set){P : D → Set} →
           ({x : D} → N x → ({y : D} → N y → R y x → P y) → P x) →
           {x : D} → (Nx : N x) → AccN R Nx → P x
accFoldN R f Nx (accN .Nx h) = f Nx (λ Ny y<x → accFoldN R f Ny (h Ny y<x))

wfIndN : {R : D → D → Set} {P : D → Set} →
         WellFoundedN R →
         ({x : D} → N x → ({y : D} → N y → R y x → P y) → P x) →
         {x : D} → N x → P x
wfIndN {R = R} wf f Nx = accFoldN R f Nx (wf Nx)

------------------------------------------------------------------------------
-- LT is well-founded

-- Adapted from http://www.iis.sinica.edu.tw/~scm/2008/well-founded-recursion-and-accessibility/ and http://code.haskell.org/~dolio/agda-share/induction/.

access : {m : D} → N m → {n : D} → (Nn : N n) → LT n m → AccN LT Nn
access zN      Nn      n<0   = ⊥-elim (¬x<0 Nn n<0)
access (sN Nm) zN      0<Sm  = accN zN (λ Nn' n'<0 → ⊥-elim (¬x<0 Nn' n'<0))
access (sN Nm) (sN Nn) Sn<Sm =
  accN (sN Nn) (λ Nn' n'<Sn →
    access Nm Nn' (Sx≤y→x<y Nn' Nm
                            (≤-trans (sN Nn') (sN Nn) Nm
                                     (x<y→Sx≤y Nn' (sN Nn) n'<Sn)
                                     (Sx≤Sy→x≤y (sN Nn) Nm (x<y→Sx≤y (sN Nn)
                                                                     (sN Nm)
                                                                     Sn<Sm)))))

wf-LT : WellFoundedN LT
wf-LT Nx = accN Nx (access Nx)

------------------------------------------------------------------------------
-- Well-founded induction on N

wfIndN-LT :
   (P : D → Set) →
   ({m : D} → N m → ({n : D} → N n → LT n m → P n ) → P m ) →
   {n : D} → N n → P n
wfIndN-LT P accH Nn = wfIndN {LT} {λ x → P x} wf-LT accH Nn
