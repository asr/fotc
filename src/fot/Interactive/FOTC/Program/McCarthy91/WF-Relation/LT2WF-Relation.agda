------------------------------------------------------------------------------
-- Property <→◁
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- The <→◁ property proves that the recursive calls of the McCarthy 91
-- function are on smaller arguments.

module Interactive.FOTC.Program.McCarthy91.WF-Relation.LT2WF-Relation where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.Properties using ( S∸S )
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.Inequalities.EliminationProperties using ( x<0→⊥ )
open import Interactive.FOTC.Data.Nat.Inequalities.Properties
open import Interactive.FOTC.Data.Nat.UnaryNumbers
open import Interactive.FOTC.Data.Nat.UnaryNumbers.Totality
  using ( 100-N
        ; 101-N
        )
open import Interactive.FOTC.Program.McCarthy91.WF-Relation

------------------------------------------------------------------------------

-- TODO (2019-06-09): Missing proofs.
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

<→◁-helper (nsucc {n} Nn) (nsucc {m} Nm) (nsucc {k} Nk) p qn qm h =
  k∸Sn<k∸Sm→Sk∸SSn<Sk∸SSm (<→◁-helper Nn Nm Nk m<n Sn<k Sm<k k∸n<k∸m)
  where
  postulate
    k∸Sn<k∸Sm→Sk∸SSn<Sk∸SSm : k ∸ succ₁ n < k ∸ succ₁ m →
                              succ₁ k ∸ succ₁ (succ₁ n) < succ₁ k ∸ succ₁ (succ₁ m)

  postulate
    m<n     : m < n
    Sn<k    : succ₁ n < k
    Sm<k    : succ₁ m < k
    k∸n<k∸m : k ∸ n < k ∸ m

-- TODO (2019-06-09): Missing proofs.
<→◁ : ∀ {n m} → N n → N m → m ≯ 100' → m < n → n ◁ m
<→◁ nzero          Nm    p h = ⊥-elim (x<0→⊥ Nm h)
<→◁ (nsucc {n} Nn) nzero p h = prfS0
  where
  postulate prfS0 : succ₁ n ◁ zero

<→◁ (nsucc {n} Nn) (nsucc {m} Nm) p h with x<y∨x≥y Nn 100-N
... | inj₁ n<100 = <→◁-helper Nn Nm 101-N m<n Sn≤101 Sm≤101
                              (<→◁ Nn Nm m≯100 m<n)
  where
  postulate
    m≯100  : m ≯ 100'
    m<n    : m < n
    Sn≤101 : succ₁ n < 101'
    Sm≤101 : succ₁ m < 101'

... | inj₂ n≥100 = prf-n≥100
  where
  postulate
    0≡101∸Sn : zero ≡ 101' ∸ succ₁ n
    0<101∸Sm : zero < 101' ∸ succ₁ m

  prf-n≥100 : succ₁ n ◁ succ₁ m
  prf-n≥100 = subst (λ t → t < 101' ∸ succ₁ m) 0≡101∸Sn 0<101∸Sm
