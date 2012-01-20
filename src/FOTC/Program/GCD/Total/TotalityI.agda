------------------------------------------------------------------------------
-- Totality properties of the gcd
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.GCD.Total.TotalityI where

open import Common.Function

open import FOTC.Base
open import FOTC.Base.Properties
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationProperties
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Program.GCD.Total.Definitions
open import FOTC.Program.GCD.Total.EquationsI
open import FOTC.Program.GCD.Total.GCD

------------------------------------------------------------------------------
-- gcd 0 0 is total.
gcd-00-N : N (gcd zero zero)
gcd-00-N = subst N (sym $ gcd-00) zN

------------------------------------------------------------------------------
-- gcd 0 (succ n) is total.
gcd-0S-N : ∀ {n} → N n → N (gcd zero (succ₁ n))
gcd-0S-N {n} Nn = subst N (sym $ gcd-0S n) (sN Nn)

------------------------------------------------------------------------------
-- gcd (succ₁ n) 0 is total.
gcd-S0-N : ∀ {n} → N n → N (gcd (succ₁ n) zero)
gcd-S0-N {n} Nn = subst N (sym $ gcd-S0 n) (sN Nn)

------------------------------------------------------------------------------
-- gcd (succ₁ m) (succ₁ n) when succ₁ m > succ₁ n is total.
gcd-S>S-N : ∀ {m n} → N m → N n →
            N (gcd (succ₁ m ∸ succ₁ n) (succ₁ n)) →
            GT (succ₁ m) (succ₁ n) →
            N (gcd (succ₁ m) (succ₁ n))
gcd-S>S-N {m} {n} Nm Nn ih Sm>Sn = subst N (sym $ gcd-S>S m n Sm>Sn) ih

------------------------------------------------------------------------------
-- gcd (succ₁ m) (succ₁ n) when succ₁ m ≯ succ₁ n is total.
gcd-S≯S-N : ∀ {m n} → N m → N n →
            N (gcd (succ₁ m) (succ₁ n ∸ succ₁ m)) →
            NGT (succ₁ m) (succ₁ n) →
            N (gcd (succ₁ m) (succ₁ n))
gcd-S≯S-N {m} {n} Nm Nn ih Sm≯Sn = subst N (sym $ gcd-S≯S m n Sm≯Sn) ih

------------------------------------------------------------------------------
-- gcd m n when m > n is total.
gcd-x>y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → N (gcd o p)) →
  GT m n →
  N (gcd m n)
gcd-x>y-N zN          Nn          _    0>n   = ⊥-elim $ 0>x→⊥ Nn 0>n
gcd-x>y-N (sN Nm)     zN          _    _     = gcd-S0-N Nm
gcd-x>y-N (sN {m} Nm) (sN {n} Nn) accH Sm>Sn = gcd-S>S-N Nm Nn ih Sm>Sn
  where
  -- Inductive hypothesis.
  ih : N (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))
  ih = accH {succ₁ m ∸ succ₁ n}
            {succ₁ n}
            (∸-N (sN Nm) (sN Nn))
            (sN Nn)
            ([Sx∸Sy,Sy]<[Sx,Sy] Nm Nn)

------------------------------------------------------------------------------
-- gcd m n when m ≯ n is total.
gcd-x≯y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → N (gcd o p)) →
  NGT m n →
  N (gcd m n)
gcd-x≯y-N zN          zN          _    _     = gcd-00-N
gcd-x≯y-N zN          (sN Nn)     _    _     = gcd-0S-N Nn
gcd-x≯y-N (sN {m} Nm) zN          _    Sm≯0  = ⊥-elim $ S≯0→⊥ Sm≯0
gcd-x≯y-N (sN {m} Nm) (sN {n} Nn) accH Sm≯Sn = gcd-S≯S-N Nm Nn ih Sm≯Sn
  where
  -- Inductive hypothesis.
  ih : N (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))
  ih = accH {succ₁ m}
            {succ₁ n ∸ succ₁ m}
            (sN Nm)
            (∸-N (sN Nn) (sN Nm))
            ([Sx,Sy∸Sx]<[Sx,Sy] Nm Nn)

------------------------------------------------------------------------------
-- gcd m n is total.
gcd-N : ∀ {m n} → N m → N n → N (gcd m n)
gcd-N = wfInd-LT₂ P istep
  where
  P : D → D → Set
  P i j = N (gcd i j)

  istep : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → LT₂ k l i j → P k l) →
          P i j
  istep Ni Nj accH =
    [ gcd-x>y-N Ni Nj accH
    , gcd-x≯y-N Ni Nj accH
    ] (x>y∨x≯y Ni Nj)
