------------------------------------------------------------------------------
-- Totality properties of the gcd
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.GCD.Total.TotalityATP where

open import Common.Function

open import FOTC.Base
open import FOTC.Base.Properties
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicATP
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationProperties
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Program.GCD.Total.Definitions
open import FOTC.Program.GCD.Total.GCD

------------------------------------------------------------------------------
-- gcd 0 0 is total.
postulate gcd-00-N : N (gcd zero zero)
{-# ATP prove gcd-00-N #-}

------------------------------------------------------------------------------
-- gcd 0 (succ n) is total.
postulate gcd-0S-N : ∀ {n} → N n → N (gcd zero (succ₁ n))
{-# ATP prove gcd-0S-N #-}

------------------------------------------------------------------------------
-- gcd (succ₁ n) 0 is total.
postulate gcd-S0-N : ∀ {n} → N n → N (gcd (succ₁ n) zero)
{-# ATP prove gcd-S0-N #-}

------------------------------------------------------------------------------
-- gcd (succ₁ m) (succ₁ n) when succ₁ m > succ₁ n is total.
postulate
  gcd-S>S-N : ∀ {m n} → N m → N n →
              N (gcd (succ₁ m ∸ succ₁ n) (succ₁ n)) →
              GT (succ₁ m) (succ₁ n) →
              N (gcd (succ₁ m) (succ₁ n))
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove gcd-S>S-N #-}

------------------------------------------------------------------------------
-- gcd (succ₁ m) (succ₁ n) when succ₁ m ≯ succ₁ n is total.
postulate
  gcd-S≯S-N : ∀ {m n} → N m → N n →
              N (gcd (succ₁ m) (succ₁ n ∸ succ₁ m)) →
              NGT (succ₁ m) (succ₁ n) →
              N (gcd (succ₁ m) (succ₁ n))
{-# ATP prove gcd-S≯S-N #-}

------------------------------------------------------------------------------
-- gcd m n when m > n is total.
gcd-x>y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → N (gcd o p)) →
  GT m n →
  N (gcd m n)
gcd-x>y-N zN          Nn          _    0>n   = ⊥-elim $ 0>x→⊥ Nn 0>n
gcd-x>y-N (sN Nm)     zN          _    _     = gcd-S0-N Nm
gcd-x>y-N (sN {m} Nm) (sN {n} Nn) accH Sm>Sn =
  gcd-S>S-N Nm Nn ih Sm>Sn
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
gcd-x≯y-N zN         zN           _    _     = gcd-00-N
gcd-x≯y-N zN         (sN Nn)      _    _     = gcd-0S-N Nn
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
