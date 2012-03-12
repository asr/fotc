------------------------------------------------------------------------------
-- Totality properties of the gcd
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Program.GCD.Partial.TotalityATP where

open import Common.Function

open import LTC-PCF.Base
open import LTC-PCF.Base.Properties
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Induction.NonAcc.LexicographicATP
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.EliminationProperties
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP
open import LTC-PCF.Data.Nat.PropertiesATP
open import LTC-PCF.Program.GCD.Partial.Definitions
open import LTC-PCF.Program.GCD.Partial.GCD
open import LTC-PCF.Program.GCD.Partial.EquationsATP

------------------------------------------------------------------------------
-- gcd 0 (succ n) is total.
postulate gcd-0S-N : ∀ {n} → N n → N (gcd zero (succ₁ n))
{-# ATP prove gcd-0S-N gcd-0S #-}

------------------------------------------------------------------------------
-- gcd (succ₁ n) 0 is total.
postulate gcd-S0-N : ∀ {n} → N n → N (gcd (succ₁ n) zero)
{-# ATP prove gcd-S0-N gcd-S0 #-}

------------------------------------------------------------------------------
-- gcd (succ₁ m) (succ₁ n) when succ₁ m > succ₁ n is total.
postulate
  gcd-S>S-N : ∀ {m n} → N m → N n →
              N (gcd (succ₁ m ∸ succ₁ n) (succ₁ n)) →
              GT (succ₁ m) (succ₁ n) →
              N (gcd (succ₁ m) (succ₁ n))
{-# ATP prove gcd-S>S-N gcd-S>S #-}

------------------------------------------------------------------------------
-- gcd (succ₁ m) (succ₁ n) when succ₁ m ≯ succ₁ n is total.
postulate
  gcd-S≯S-N : ∀ {m n} → N m → N n →
              N (gcd (succ₁ m) (succ₁ n ∸ succ₁ m)) →
              NGT (succ₁ m) (succ₁ n) →
              N (gcd (succ₁ m) (succ₁ n))
{-# ATP prove gcd-S≯S-N gcd-S≯S #-}

------------------------------------------------------------------------------
-- gcd m n when m > n is total.
gcd-x>y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → x≢0≢y o p → N (gcd o p)) →
  GT m n →
  x≢0≢y m n →
  N (gcd m n)
gcd-x>y-N zN Nn _ 0>n _ = ⊥-elim $ 0>x→⊥ Nn 0>n
gcd-x>y-N (sN Nm) zN _ _ _  = gcd-S0-N Nm
gcd-x>y-N (sN {m} Nm) (sN {n} Nn) accH Sm>Sn _ =
  gcd-S>S-N Nm Nn ih Sm>Sn
  where
  -- Inductive hypothesis.
  ih : N (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))
  ih = accH {succ₁ m ∸ succ₁ n}
            {succ₁ n}
            (∸-N (sN Nm) (sN Nn))
            (sN Nn)
            ([Sx∸Sy,Sy]<[Sx,Sy] Nm Nn)
            (λ p → ⊥-elim $ S≢0 $ ∧-proj₂ p)

------------------------------------------------------------------------------
-- gcd m n when m ≯ n is total.
gcd-x≯y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → x≢0≢y o p → N (gcd o p)) →
  NGT m n →
  x≢0≢y m n →
  N (gcd m n)
gcd-x≯y-N zN          zN          _    _     h = ⊥-elim $ h (refl , refl)
gcd-x≯y-N zN          (sN Nn)     _    _     _ = gcd-0S-N Nn
gcd-x≯y-N (sN _)      zN          _    Sm≯0  _ = ⊥-elim $ S≯0→⊥ Sm≯0
gcd-x≯y-N (sN {m} Nm) (sN {n} Nn) accH Sm≯Sn _ = gcd-S≯S-N Nm Nn ih Sm≯Sn
  where
  -- Inductive hypothesis.
  ih : N (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))
  ih = accH {succ₁ m}
            {succ₁ n ∸ succ₁ m}
            (sN Nm)
            (∸-N (sN Nn) (sN Nm))
            ([Sx,Sy∸Sx]<[Sx,Sy] Nm Nn)
            (λ p → ⊥-elim $ S≢0 $ ∧-proj₁ p)

------------------------------------------------------------------------------
-- gcd m n when m ≢ 0 and n ≢ 0 is total.
gcd-N : ∀ {m n} → N m → N n → x≢0≢y m n → N (gcd m n)
gcd-N = wfInd-LT₂ A istep
  where
  A : D → D → Set
  A i j = x≢0≢y i j → N (gcd i j)

  istep : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → LT₂ k l i j → A k l) →
          A i j
  istep Ni Nj accH =
    [ gcd-x>y-N Ni Nj accH
    , gcd-x≯y-N Ni Nj accH
    ] (x>y∨x≯y Ni Nj)
