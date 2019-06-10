------------------------------------------------------------------------------
-- Properties for the relation _◁_
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.McCarthy91.WF-Relation.Properties where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.Inequalities.EliminationProperties
  using ( x<y→y<x→⊥ )
open import Interactive.FOTC.Data.Nat.Inequalities.Properties
  using ( x∸y<Sx
        ; <-trans
        ; x<y→y≤z→x<z
        ; x∸Sy≤x∸y
        )
open import Interactive.FOTC.Data.Nat.Properties
  using ( ∸-N
        ; S∸S
        )
open import Interactive.FOTC.Data.Nat.UnaryNumbers
open import Interactive.FOTC.Data.Nat.UnaryNumbers.Totality using ( 101-N )
open import Interactive.FOTC.Program.McCarthy91.Arithmetic
open import Interactive.FOTC.Program.McCarthy91.WF-Relation

------------------------------------------------------------------------------

◁-fn-N : ∀ {n} → N n → N (◁-fn n)
◁-fn-N Nn = ∸-N 101-N Nn

-- TODO (2019-06-09): Missing proofs.
0◁x→⊥ : ∀ {n} → N n → ¬ (zero ◁ n)
0◁x→⊥ nzero 0◁n = prf
  where
  postulate prf : ⊥

0◁x→⊥ (nsucc Nn) 0◁Sn = prf
  where
  postulate prf : ⊥

◁-trans : ∀ {m n o} → N m → N n → N o → m ◁ n → n ◁ o → m ◁ o
◁-trans Nm Nn No m◁n n◁o =
  <-trans (∸-N 101-N Nm) (∸-N 101-N Nn) (∸-N 101-N No) m◁n n◁o

-- TODO (2019-06-09): Missing proofs.
Sx◁Sy→x◁y : ∀ {m n} → N m → N n → succ₁ m ◁ succ₁ n → m ◁ n
Sx◁Sy→x◁y nzero nzero S0◁S0 = prf
  where
  postulate prf : zero ◁ zero

Sx◁Sy→x◁y nzero (nsucc {n} Nn) S0◁SSn = prf
  where
  postulate prf : zero ◁ succ₁ n

Sx◁Sy→x◁y (nsucc {m} Nm) nzero SSm◁S0 = prf
  where
  postulate prf : succ₁ m ◁ zero

Sx◁Sy→x◁y (nsucc {m} Nm) (nsucc {n} Nn) SSm◁SSn = prf
  where
  postulate prf : succ₁ m ◁ succ₁ n

x◁Sy→x◁y : ∀ {m n} → N m → N n → m ◁ succ₁ n → m ◁ n
x◁Sy→x◁y {n = n} nzero Nn 0◁Sn = ⊥-elim (0◁x→⊥ (nsucc Nn) 0◁Sn)

-- TODO (2019-06-09): Missing proof.
x◁Sy→x◁y (nsucc {m} Nm) nzero Sm◁S0 = prf
   where
   postulate prf : succ₁ m ◁ zero

x◁Sy→x◁y (nsucc {m} Nm) (nsucc {n} Nn) Sm◁SSn =
  x<y→y≤z→x<z (∸-N 101-N (nsucc Nm))
              (∸-N 101-N (nsucc (nsucc Nn)))
              (∸-N 101-N (nsucc Nn))
              Sm◁SSn
              (x∸Sy≤x∸y 101-N (nsucc Nn))
