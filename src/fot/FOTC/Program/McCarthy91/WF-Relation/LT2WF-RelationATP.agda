------------------------------------------------------------------------------
-- Property <→◁
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- The <→◁ property proves that the recursive calls of the McCarthy 91
-- function are on smaller arguments.

module FOTC.Program.McCarthy91.WF-Relation.LT2WF-RelationATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.PropertiesATP using ( S∸S )
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationPropertiesATP using ( x<0→⊥ )
open import FOTC.Data.Nat.Inequalities.PropertiesATP
  using ( x<y→x≤y
        ; x≥y→y>0→x∸y<x
        ; x∸y<Sx
        ; x<y∨x≥y
        ; Sx≯y→x≯y
        ; x≯y→x≤y
        ; x≤y→x∸y≡0
        ; x<y→0<y∸x
        )
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP
  using ( 100-N
        ; 101-N
        )
open import FOTC.Program.McCarthy91.WF-Relation

------------------------------------------------------------------------------

<→◁-helper : ∀ {n m k} → N n → N m → N k →
             m < n → succ₁ n < k →
             succ₁ m < k →
             k ∸ n < k ∸ m →
             k ∸ succ₁ n < k ∸ succ₁ m
<→◁-helper nzero Nm Nk p qn qm h = ⊥-elim (x<0→⊥ Nm p)
<→◁-helper (nsucc Nn) Nm nzero p qn qm h = ⊥-elim (x<0→⊥ (nsucc Nm) qm)
<→◁-helper (nsucc {n} Nn) nzero (nsucc {k} Nk) p qn qm h = prfS0S
  where
  postulate
    k≥Sn   : k ≥ succ₁ n
    k∸Sn<k : k ∸ (succ₁ n) < k
    prfS0S : succ₁ k ∸ succ₁ (succ₁ n) < succ₁ k ∸ succ₁ zero
  {-# ATP prove k≥Sn x<y→x≤y #-}
  {-# ATP prove k∸Sn<k k≥Sn x≥y→y>0→x∸y<x #-}
  {-# ATP prove prfS0S k∸Sn<k S∸S #-}

<→◁-helper (nsucc {n} Nn) (nsucc {m} Nm) (nsucc {k} Nk) p qn qm h =
  k∸Sn<k∸Sm→Sk∸SSn<Sk∸SSm (<→◁-helper Nn Nm Nk m<n Sn<k Sm<k k∸n<k∸m)
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

-- 25 June 2014. Requires the TERMINATING flag when using
-- --without-K. See Agda issue 1214.

{-# TERMINATING #-}
<→◁ : ∀ {n m} → N n → N m → m ≯ 100' → m < n → n ◁ m
<→◁ nzero          Nm    p h = ⊥-elim (x<0→⊥ Nm h)
<→◁ (nsucc {n} Nn) nzero p h = prfS0
  where
  postulate prfS0 : succ₁ n ◁ zero
  {-# ATP prove prfS0 x∸y<Sx S∸S #-}

<→◁ (nsucc {n} Nn) (nsucc {m} Nm) p h with x<y∨x≥y Nn 100-N
... | inj₁ n<100 = <→◁-helper Nn Nm 101-N m<n Sn≤101 Sm≤101
                              (<→◁ Nn Nm m≯100 m<n)
  where
  postulate
    m≯100  : m ≯ 100'
    m<n    : m < n
    Sn≤101 : succ₁ n < 101'
    Sm≤101 : succ₁ m < 101'
  {-# ATP prove m≯100 Sx≯y→x≯y #-}
  {-# ATP prove m<n #-}
  {-# ATP prove Sn≤101 #-}
  {-# ATP prove Sm≤101 x≯y→x≤y #-}
... | inj₂ n≥100 = prf-n≥100
  where
  postulate
    0≡101∸Sn : zero ≡ 101' ∸ succ₁ n
    0<101∸Sm : zero < 101' ∸ succ₁ m
  {-# ATP prove 0≡101∸Sn x≤y→x∸y≡0 #-}
  {-# ATP prove 0<101∸Sm x≯y→x≤y x<y→0<y∸x #-}

  prf-n≥100 : succ₁ n ◁ succ₁ m
  prf-n≥100 = subst (λ t → t < 101' ∸ succ₁ m) 0≡101∸Sn 0<101∸Sm
