------------------------------------------------------------------------------
-- Totality properties of the gcd
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Program.GCD.Partial.Totality where

open import Common.Function

open import LTC-PCF.Base
open import LTC-PCF.Base.Properties
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Induction.NonAcc.Lexicographic
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.EliminationProperties
open import LTC-PCF.Data.Nat.Inequalities.Properties
open import LTC-PCF.Data.Nat.Properties
open import LTC-PCF.Program.GCD.Partial.Definitions
open import LTC-PCF.Program.GCD.Partial.GCD
open import LTC-PCF.Program.GCD.Partial.Equations

------------------------------------------------------------------------------
-- gcd 0 (succ n) is total.
gcd-0S-N : ∀ {n} → N n → N (gcd zero (succ₁ n))
gcd-0S-N {n} Nn = subst N (sym $ gcd-0S n) (nsucc Nn)

------------------------------------------------------------------------------
-- gcd (succ₁ n) 0 is total.
gcd-S0-N : ∀ {n} → N n → N (gcd (succ₁ n) zero)
gcd-S0-N {n} Nn = subst N (sym $ gcd-S0 n) (nsucc Nn)

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
  (∀ {o p} → N o → N p → Lexi o p m n → x≢0≢y o p → N (gcd o p)) →
  GT m n →
  x≢0≢y m n →
  N (gcd m n)
gcd-x>y-N nzero          Nn             _    0>n   _ = ⊥-elim $ 0>x→⊥ Nn 0>n
gcd-x>y-N (nsucc Nm)     nzero          _    _     _ = gcd-S0-N Nm
gcd-x>y-N (nsucc {m} Nm) (nsucc {n} Nn) accH Sm>Sn _ =
  gcd-S>S-N Nm Nn ih Sm>Sn
  where
  -- Inductive hypothesis.
  ih : N (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))
  ih = accH {succ₁ m ∸ succ₁ n}
            {succ₁ n}
            (∸-N (nsucc Nm) (nsucc Nn))
            (nsucc Nn)
            ([Sx∸Sy,Sy]<[Sx,Sy] Nm Nn)
            (λ p → ⊥-elim $ S≢0 $ ∧-proj₂ p)

------------------------------------------------------------------------------
-- gcd m n when m ≯ n is total.
gcd-x≯y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → Lexi o p m n → x≢0≢y o p → N (gcd o p)) →
  NGT m n →
  x≢0≢y m n →
  N (gcd m n)
gcd-x≯y-N nzero          nzero          _    _     h = ⊥-elim $ h (refl , refl)
gcd-x≯y-N nzero          (nsucc Nn)     _    _     _ = gcd-0S-N Nn
gcd-x≯y-N (nsucc _)      nzero          _    Sm≯0  _ = ⊥-elim $ S≯0→⊥ Sm≯0
gcd-x≯y-N (nsucc {m} Nm) (nsucc {n} Nn) accH Sm≯Sn _ = gcd-S≯S-N Nm Nn ih Sm≯Sn
  where
  -- Inductive hypothesis.
  ih : N (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))
  ih = accH {succ₁ m}
            {succ₁ n ∸ succ₁ m}
            (nsucc Nm)
            (∸-N (nsucc Nn) (nsucc Nm))
            ([Sx,Sy∸Sx]<[Sx,Sy] Nm Nn)
            (λ p → ⊥-elim $ S≢0 $ ∧-proj₁ p)

------------------------------------------------------------------------------
-- gcd m n when m ≢ 0 and n ≢ 0 is total.
gcd-N : ∀ {m n} → N m → N n → x≢0≢y m n → N (gcd m n)
gcd-N = Lexi-wfind A istep
  where
  A : D → D → Set
  A i j = x≢0≢y i j → N (gcd i j)

  istep : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → Lexi k l i j → A k l) →
          A i j
  istep Ni Nj accH = case (gcd-x>y-N Ni Nj accH)
                          (gcd-x≯y-N Ni Nj accH)
                          (x>y∨x≯y Ni Nj)
