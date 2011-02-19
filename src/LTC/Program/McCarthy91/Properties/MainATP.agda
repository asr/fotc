------------------------------------------------------------------------------
-- Main properties of the McCarthy 91 function
------------------------------------------------------------------------------

-- The main properties proved of the McCarthy 91 function (called
-- mc91) are

-- 1. The function always terminates.
-- 2. For all n, n < mc91 n + 11.
-- 3. For all n > 100, then mc91 n = n - 10.
-- 4. For all n <= 100, then mc91 n = 91.

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module LTC.Program.McCarthy91.Properties.MainATP where

open import LTC.Base

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesATP
open import LTC.Data.Nat.Unary.Numbers
open import LTC.Data.Nat.Unary.IsN-ATP
open import LTC.Data.Nat.Unary.Inequalities.PropertiesATP

open import LTC.Program.McCarthy91.ArithmeticATP
open import LTC.Program.McCarthy91.McCarthy91
open import LTC.Program.McCarthy91.MCR
open import LTC.Program.McCarthy91.MCR.LT2MCR-ATP
open import LTC.Program.McCarthy91.MCR.WellFoundedInductionATP
open import LTC.Program.McCarthy91.Properties.AuxiliaryATP

------------------------------------------------------------------------------

mc91-N-ineq : ∀ {n} → N n → N (mc91 n) ∧ LT n (mc91 n + eleven)
mc91-N-ineq = wfInd-MCR P mc91-N-ineq-aux
  where
    P : D → Set
    P d = N (mc91 d) ∧ LT d (mc91 d + eleven)

    mc91-N-ineq-aux : ∀ {m} → N m → (∀ {k} → N k → MCR k m → P k) → P m
    mc91-N-ineq-aux {m} Nm f with x>y∨x≤y Nm N100
    ... | inj₁ m>100 = ( Nmc91>100 Nm m>100 , x<mc91x+11>100 Nm m>100 )
    ... | inj₂ m≤100 =
      let Nm+11 : N (m + eleven)
          Nm+11 = x+11-N Nm

          ih1 : P (m + eleven)
          ih1 = f Nm+11 (LT2MCR (x+11-N Nm) Nm m≤100 (x<x+11 Nm))

          Nih1 : N (mc91 (m + eleven))
          Nih1 = ∧-proj₁ ih1

          LTih1 : LT (m + eleven) (mc91 (m + eleven) + eleven)
          LTih1 = ∧-proj₂ ih1

          m<mc91m+11 : LT m (mc91 (m + eleven))
          m<mc91m+11 = x+k<y+k→x<y Nm Nih1 N11 LTih1

          ih2 : P (mc91 (m + eleven))
          ih2 = f Nih1 (LT2MCR Nih1 Nm m≤100 m<mc91m+11)

          Nmc91≤100 : N (mc91 m)
          Nmc91≤100 = Nmc91≤100' m m≤100 (∧-proj₁ ih2)

      in ( Nmc91≤100 ,
           <-trans Nm Nih1 (x+11-N Nmc91≤100)
                   m<mc91m+11
                   (mc91x+11<mc91x+11 m m≤100 (∧-proj₂ ih2)))

mc91-res : ∀ {n} → N n → (GT n one-hundred ∧ mc91 n ≡ n ∸ ten) ∨
                         (LE n one-hundred ∧ mc91 n ≡ ninety-one)
mc91-res = wfInd-MCR P mc91-res-aux
  where
    P : D → Set
    P d = (GT d one-hundred ∧ mc91 d ≡ d ∸ ten) ∨
          (LE d one-hundred ∧ mc91 d ≡ ninety-one)

    mc91-res-aux : ∀ {m} → N m → (∀ {k} → N k → MCR k m → P k) → P m
    mc91-res-aux {m} Nm f with x>y∨x≤y Nm N100
    ... | inj₁ m>100 = inj₁ ( m>100 , mc91-eq₁ m m>100 )
    ... | inj₂ m≤100 with x<Sy→x<y∨x≡y Nm N100 m≤100
    ... | inj₂ m≡100 = inj₂ ( m≤100 , mc91-res-100' m≡100 )
    ... | inj₁ m≤99 with x<Sy→x<y∨x≡y Nm N99 m≤99
    ... | inj₂ m≡99 = inj₂ ( m≤100 , mc91-res-99' m≡99 )
    ... | inj₁ m≤98 with x<Sy→x<y∨x≡y Nm N98 m≤98
    ... | inj₂ m≡98 = inj₂ ( m≤100 , mc91-res-98' m≡98 )
    ... | inj₁ m≤97 with x<Sy→x<y∨x≡y Nm N97 m≤97
    ... | inj₂ m≡97 = inj₂ ( m≤100 , mc91-res-97' m≡97 )
    ... | inj₁ m≤96 with x<Sy→x<y∨x≡y Nm N96 m≤96
    ... | inj₂ m≡96 = inj₂ ( m≤100 , mc91-res-96' m≡96 )
    ... | inj₁ m≤95 with x<Sy→x<y∨x≡y Nm N95 m≤95
    ... | inj₂ m≡95 = inj₂ ( m≤100 , mc91-res-95' m≡95 )
    ... | inj₁ m≤94 with x<Sy→x<y∨x≡y Nm N94 m≤94
    ... | inj₂ m≡94 = inj₂ ( m≤100 , mc91-res-94' m≡94 )
    ... | inj₁ m≤93 with x<Sy→x<y∨x≡y Nm N93 m≤93
    ... | inj₂ m≡93 = inj₂ ( m≤100 , mc91-res-93' m≡93 )
    ... | inj₁ m≤92 with x<Sy→x<y∨x≡y Nm N92 m≤92
    ... | inj₂ m≡92 = inj₂ ( m≤100 , mc91-res-92' m≡92 )
    ... | inj₁ m≤91 with x<Sy→x<y∨x≡y Nm N91 m≤91
    ... | inj₂ m≡91 = inj₂ ( m≤100 , mc91-res-91' m≡91 )
    ... | inj₁ m≤90 with x<Sy→x<y∨x≡y Nm N90 m≤90
    ... | inj₂ m≡90 = inj₂ ( m≤100 , mc91-res-90' m≡90 )
    ... | inj₁ m≤89 =  inj₂ ( m≤100 , mc91-res-m≤89 )

      where mc91-res-m+11 : mc91 (m + eleven) ≡ ninety-one
            mc91-res-m+11 with f (x+11-N Nm)
                                 (LT2MCR (x+11-N Nm) Nm m≤100 (x<x+11 Nm))
            ... | inj₁ ( m+11>100 , _) = ⊥-elim (x≤89→x+11>100→⊥ Nm
                                                m≤89 m+11>100)
            ... | inj₂ ( _ , res ) = res

            mc91-res-m≤89 : mc91 m ≡ ninety-one
            mc91-res-m≤89 = mc91x-res≤100 m ninety-one m≤100
                                          mc91-res-m+11 mc91-res-91

------------------------------------------------------------------------------
-- Main properties

-- The function always terminates.
mc91-N : ∀ {n} → N n → N (mc91 n)
mc91-N Nn = ∧-proj₁ (mc91-N-ineq Nn)

-- For all n, n < mc91 n + 11.
mc91-ineq : ∀ {n} → N n → LT n (mc91 n + eleven)
mc91-ineq Nn = ∧-proj₂ (mc91-N-ineq Nn)

-- For all n > 100, then mc91 n = n - 10.
mc91-res>100 : ∀ {n} → N n → GT n one-hundred → mc91 n ≡ n ∸ ten
mc91-res>100 Nn n>100  with mc91-res Nn
... | inj₁ ( _ , res ) = res
... | inj₂ ( n≤100 , _ ) = ⊥-elim (x>y→x≤y→⊥ Nn N100 n>100 n≤100)

-- For all n <= 100, then mc91 n = 91.
mc91-res≤100 : ∀ {n} → N n → LE n one-hundred → mc91 n ≡ ninety-one
mc91-res≤100 Nn n≤100  with mc91-res Nn
... | inj₁ ( n>100 , _ ) = ⊥-elim (x>y→x≤y→⊥ Nn N100 n>100 n≤100)
... | inj₂ ( _ , res ) = res
