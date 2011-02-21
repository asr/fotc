----------------------------------------------------------------------------
-- Well-founded induction on LT using the accesibility relation
----------------------------------------------------------------------------


module Draft.Accesibility.WellFoundedInduction where

open import FOTC.Base

open import Common.Function

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI

----------------------------------------------------------------------------
-- Accesibility stuff for the FOTC natural numbers

-- Adapted from
-- http://www.iis.sinica.edu.tw/~scm/2008/well-founded-recursion-and-accessibility/

data AccN (_<_ : D → D → Set) : D → Set where
 accN : ∀ {x} → N x → (∀ {y} → N y → y < x → AccN _<_ y) → AccN _<_ x

acc-elimN : (_<_ : D → D → Set) {P : D → Set} →
            (∀ {x} → N x → (∀ {y} → N y → y < x → AccN _<_ y) →
                 (∀ {y} → N y → y < x → P y) → P x) →
            ∀ {x} → N x → AccN _<_ x → P x
acc-elimN _<_ Φ Nx (accN _ h) = Φ Nx h (λ Ny y<x → acc-elimN _<_ Φ Ny (h Ny y<x))

acc-foldN : (R : D → D → Set) {P : D → Set} →
            (∀ {x} → N x → (∀ {y} → N y → R y x → P y) → P x) →
            ∀ {x} → N x → AccN R x → P x
acc-foldN R f Nx (accN _ h) = f Nx (λ Ny yRx → acc-foldN R f Ny (h Ny yRx))

well-foundN : (D → D → Set) → Set
well-foundN _<_ = ∀ {x} → N x → AccN _<_ x

rec-wfN : {_<_ : D → D → Set} {P : D → Set} →
          well-foundN _<_ →
          (∀ {x} → N x → (∀ {y} → N y → y < x → P y) → P x) →
          ∀ {x} → N x → P x
rec-wfN {_<_} wf f Nx = acc-foldN _<_ f Nx (wf Nx)

-- The LT relation is well-founded.
LT-wf : well-foundN LT
LT-wf Nn = accN Nn (helper Nn)

  where
    helper : ∀ {m n} → N m → N n → LT n m → AccN LT n
    helper zN     Nn n<0  = ⊥-elim $ x<0→⊥ Nn n<0
    helper (sN _) zN 0<Sm = accN zN (λ Nn' n'<0 → ⊥-elim $ x<0→⊥ Nn' n'<0)

    helper (sN {m} Nm) (sN {n} Nn) Sn<Sm = accN (sN Nn)
      (λ {n'} Nn' n'<Sn →
        let n<m : LT n m
            n<m = Sx<Sy→x<y Sn<Sm

            n'<m : LT n' m
            n'<m = [ (λ n'<n → <-trans Nn' Nn Nm n'<n n<m)
                   , (λ n'≡n → x≡y→y<z→x<z n'≡n n<m)
                   ] (x<Sy→x<y∨x≡y Nn' Nn n'<Sn)

        in  helper Nm Nn' n'<m
      )

wfInd-LT : (P : D → Set) →
           (∀ {m} → N m → (∀ {n} → N n → LT n m → P n) → P m) →
           ∀ {n} → N n → P n
wfInd-LT P = rec-wfN LT-wf
