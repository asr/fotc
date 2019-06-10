------------------------------------------------------------------------------
-- Totality properties of the gcd
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.GCD.Total.Totality where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Induction.NonAcc.Lexicographic
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.Inequalities.EliminationProperties
open import Combined.FOTC.Data.Nat.Inequalities.Properties
open import Combined.FOTC.Data.Nat.Properties
open import Combined.FOTC.Program.GCD.Total.Definitions
open import Combined.FOTC.Program.GCD.Total.GCD

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
postulate gcd-S>S-N : ∀ {m n} → N m → N n →
                      N (gcd (succ₁ m ∸ succ₁ n) (succ₁ n)) →
                      succ₁ m > succ₁ n →
                      N (gcd (succ₁ m) (succ₁ n))
{-# ATP prove gcd-S>S-N #-}

------------------------------------------------------------------------------
-- gcd (succ₁ m) (succ₁ n) when succ₁ m ≯ succ₁ n is total.
postulate gcd-S≯S-N : ∀ {m n} → N m → N n →
                      N (gcd (succ₁ m) (succ₁ n ∸ succ₁ m)) →
                      succ₁ m ≯ succ₁ n →
                      N (gcd (succ₁ m) (succ₁ n))
{-# ATP prove gcd-S≯S-N #-}

------------------------------------------------------------------------------
-- gcd m n when m > n is total.
gcd-x>y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → Lexi o p m n → N (gcd o p)) →
  m > n →
  N (gcd m n)
gcd-x>y-N nzero          Nn            _   0>n    = ⊥-elim (0>x→⊥ Nn 0>n)
gcd-x>y-N (nsucc Nm)     nzero          _  _     = gcd-S0-N Nm
gcd-x>y-N (nsucc {m} Nm) (nsucc {n} Nn) ah Sm>Sn =
  gcd-S>S-N Nm Nn ih Sm>Sn
  where
  -- Inductive hypothesis.
  ih : N (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))
  ih = ah {succ₁ m ∸ succ₁ n}
          {succ₁ n}
          (∸-N (nsucc Nm) (nsucc Nn))
          (nsucc Nn)
          ([Sx∸Sy,Sy]<[Sx,Sy] Nm Nn)

------------------------------------------------------------------------------
-- gcd m n when m ≯ n is total.
gcd-x≯y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → Lexi o p m n → N (gcd o p)) →
  m ≯ n →
  N (gcd m n)
gcd-x≯y-N nzero          nzero          _  _     = gcd-00-N
gcd-x≯y-N nzero          (nsucc Nn)     _  _     = gcd-0S-N Nn
gcd-x≯y-N (nsucc _)      nzero          _  Sm≯0  = ⊥-elim (S≯0→⊥ Sm≯0)
gcd-x≯y-N (nsucc {m} Nm) (nsucc {n} Nn) ah Sm≯Sn = gcd-S≯S-N Nm Nn ih Sm≯Sn
  where
  -- Inductive hypothesis.
  ih : N (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))
  ih = ah {succ₁ m}
          {succ₁ n ∸ succ₁ m}
          (nsucc Nm)
          (∸-N (nsucc Nn) (nsucc Nm))
          ([Sx,Sy∸Sx]<[Sx,Sy] Nm Nn)

------------------------------------------------------------------------------
-- gcd m n is total.
gcd-N : ∀ {m n} → N m → N n → N (gcd m n)
gcd-N = Lexi-wfind A h
  where
  A : D → D → Set
  A i j = N (gcd i j)

  h : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → Lexi k l i j → A k l) →
      A i j
  h Ni Nj ah = case (gcd-x>y-N Ni Nj ah) (gcd-x≯y-N Ni Nj ah) (x>y∨x≯y Ni Nj)
