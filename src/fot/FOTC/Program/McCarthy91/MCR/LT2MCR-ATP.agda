------------------------------------------------------------------------------
-- LT2MCR property
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The LT2MCR property proves that the recursive calls of the McCarthy
-- 91 function are on smaller arguments.

module FOTC.Program.McCarthy91.MCR.LT2MCR-ATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationProperties
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP
open import FOTC.Program.McCarthy91.MCR

------------------------------------------------------------------------------

LT2MCR-helper : ∀ {n m k} → N n → N m → N k →
                m < n → succ₁ n < k →
                succ₁ m < k →
                k ∸ n < k ∸ m →
                k ∸ succ₁ n < k ∸ succ₁ m
LT2MCR-helper nzero Nm Nk p qn qm h = ⊥-elim (x<0→⊥ Nm p)
LT2MCR-helper (nsucc Nn) Nm nzero p qn qm h = ⊥-elim (x<0→⊥ (nsucc Nm) qm)
LT2MCR-helper (nsucc {n} Nn) nzero (nsucc {k} Nk) p qn qm h = prfS0S
  where
  postulate
    k≥Sn   : k ≥ succ₁ n
    k∸Sn<k : k ∸ (succ₁ n) < k
    prfS0S : succ₁ k ∸ succ₁ (succ₁ n) < succ₁ k ∸ succ₁ zero
  {-# ATP prove k≥Sn x<y→x≤y #-}
  {-# ATP prove k∸Sn<k k≥Sn x≥y→y>0→x∸y<x #-}
  {-# ATP prove prfS0S k∸Sn<k S∸S #-}

LT2MCR-helper (nsucc {n} Nn) (nsucc {m} Nm) (nsucc {k} Nk) p qn qm h =
  k∸Sn<k∸Sm→Sk∸SSn<Sk∸SSm (LT2MCR-helper Nn Nm Nk m<n Sn<k Sm<k k∸n<k∸m)
  where
  postulate
    k∸Sn<k∸Sm→Sk∸SSn<Sk∸SSm : k ∸ succ₁ n < k ∸ succ₁ m →
                              succ₁ k ∸ succ₁ (succ₁ n) < succ₁ k ∸ succ₁ (succ₁ m)
  {-# ATP prove k∸Sn<k∸Sm→Sk∸SSn<Sk∸SSm S∸S #-}

  postulate
    m<n     : m < n
    Sn<k    : succ₁ n < k
    Sm<k    : succ₁ m < k
    k∸n<k∸m : k ∸ n < k ∸ m
  {-# ATP prove m<n #-}
  {-# ATP prove Sn<k #-}
  {-# ATP prove Sm<k #-}
  {-# ATP prove k∸n<k∸m S∸S #-}

LT2MCR : ∀ {n m} → N n → N m → m ≯ one-hundred → m < n → MCR n m
LT2MCR nzero          Nm    p h = ⊥-elim (x<0→⊥ Nm h)
LT2MCR (nsucc {n} Nn) nzero p h = prfS0
  where
  postulate prfS0 : MCR (succ₁ n) zero
  {-# ATP prove prfS0 x∸y<Sx S∸S #-}

LT2MCR (nsucc {n} Nn) (nsucc {m} Nm) p h with x<y∨x≥y Nn 100-N
... | inj₁ n<100 = LT2MCR-helper Nn Nm 101-N m<n Sn≤101 Sm≤101
                                 (LT2MCR Nn Nm m≯100 m<n)
  where
  postulate
    m≯100  : m ≯ one-hundred
    m<n    : m < n
    Sn≤101 : succ₁ n < hundred-one
    Sm≤101 : succ₁ m < hundred-one
  {-# ATP prove m≯100 Sx≯y→x≯y #-}
  {-# ATP prove m<n #-}
  {-# ATP prove Sn≤101 #-}
  {-# ATP prove Sm≤101 x≯y→x≤y #-}
... | inj₂ n≥100 = prf-n≥100
  where
  postulate
    0≡101∸Sn  : zero ≡ hundred-one ∸ succ₁ n
    0<101∸Sm  : zero < hundred-one ∸ succ₁ m
  {-# ATP prove 0≡101∸Sn x≤y→x∸y≡0 #-}
  {-# ATP prove 0<101∸Sm x≯y→x≤y x<y→0<y∸x #-}

  prf-n≥100 : MCR (succ₁ n) (succ₁ m)
  prf-n≥100 = subst (λ t → t < hundred-one ∸ succ₁ m) 0≡101∸Sn 0<101∸Sm
