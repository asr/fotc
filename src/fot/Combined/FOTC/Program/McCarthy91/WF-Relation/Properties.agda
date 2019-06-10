------------------------------------------------------------------------------
-- Properties for the relation _◁_
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.McCarthy91.WF-Relation.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.Inequalities.EliminationProperties
  using ( x<y→y<x→⊥ )
open import Combined.FOTC.Data.Nat.Inequalities.Properties
  using ( x∸y<Sx
        ; <-trans
        ; x<x∸y→⊥
        ; x∸y<x∸z→Sx∸y<Sx∸z
        ; x<y→y≤z→x<z
        ; x∸Sy≤x∸y
        )
open import Combined.FOTC.Data.Nat.Properties
  using ( ∸-N
        ; S∸S
        )
open import Combined.FOTC.Data.Nat.UnaryNumbers
open import Combined.FOTC.Data.Nat.UnaryNumbers.Totality using ( 101-N )
open import Combined.FOTC.Program.McCarthy91.Arithmetic
open import Combined.FOTC.Program.McCarthy91.WF-Relation

------------------------------------------------------------------------------

◁-fn-N : ∀ {n} → N n → N (◁-fn n)
◁-fn-N Nn = ∸-N 101-N Nn

0◁x→⊥ : ∀ {n} → N n → ¬ (zero ◁ n)
0◁x→⊥ nzero 0◁n = prf
  where
  postulate prf : ⊥
  {-# ATP prove prf #-}

0◁x→⊥ (nsucc Nn) 0◁Sn = prf
  where
  postulate prf : ⊥
  {-# ATP prove prf ∸-N x∸y<Sx x<y→y<x→⊥ S∸S #-}

◁-trans : ∀ {m n o} → N m → N n → N o → m ◁ n → n ◁ o → m ◁ o
◁-trans Nm Nn No m◁n n◁o =
  <-trans (∸-N 101-N Nm) (∸-N 101-N Nn) (∸-N 101-N No) m◁n n◁o

Sx◁Sy→x◁y : ∀ {m n} → N m → N n → succ₁ m ◁ succ₁ n → m ◁ n
Sx◁Sy→x◁y nzero nzero S0◁S0 = prf
  where
  postulate prf : zero ◁ zero
  {-# ATP prove prf #-}

Sx◁Sy→x◁y nzero (nsucc {n} Nn) S0◁SSn = prf
  where
  postulate prf : zero ◁ succ₁ n
  {-# ATP prove prf x<x∸y→⊥ S∸S #-}

Sx◁Sy→x◁y (nsucc {m} Nm) nzero SSm◁S0 = prf
  where
  postulate prf : succ₁ m ◁ zero
  {-# ATP prove prf ∸-N x∸y<Sx S∸S #-}

Sx◁Sy→x◁y (nsucc {m} Nm) (nsucc {n} Nn) SSm◁SSn = prf
  where
  postulate prf : succ₁ m ◁ succ₁ n
  -- 2018-06-27: The ATPs could not prove the theorem (300 sec), but
  -- Vampire 4.2.2, via `online-atps`, could prove it.
  --
  {-# ATP prove prf x∸y<x∸z→Sx∸y<Sx∸z S∸S #-}

x◁Sy→x◁y : ∀ {m n} → N m → N n → m ◁ succ₁ n → m ◁ n
x◁Sy→x◁y {n = n} nzero Nn 0◁Sn = ⊥-elim (0◁x→⊥ (nsucc Nn) 0◁Sn)

x◁Sy→x◁y (nsucc {m} Nm) nzero Sm◁S0 = prf
   where
   postulate prf : succ₁ m ◁ zero
   {-# ATP prove prf x∸y<Sx S∸S #-}

x◁Sy→x◁y (nsucc {m} Nm) (nsucc {n} Nn) Sm◁SSn =
  x<y→y≤z→x<z (∸-N 101-N (nsucc Nm))
              (∸-N 101-N (nsucc (nsucc Nn)))
              (∸-N 101-N (nsucc Nn))
              Sm◁SSn
              (x∸Sy≤x∸y 101-N (nsucc Nn))
