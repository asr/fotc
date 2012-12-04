------------------------------------------------------------------------------
-- Totality properties of the gcd
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.GCD.Partial.TotalityI where

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationProperties
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Program.GCD.Partial.ConversionRulesI
open import FOTC.Program.GCD.Partial.Definitions
open import FOTC.Program.GCD.Partial.GCD

------------------------------------------------------------------------------
-- gcd 0 (succ n) is total.
gcd-0S-N : ∀ {n} → N n → N (gcd zero (succ₁ n))
gcd-0S-N {n} Nn = subst N (sym (gcd-0S n)) (nsucc Nn)

------------------------------------------------------------------------------
-- gcd (succ₁ n) 0 is total.
gcd-S0-N : ∀ {n} → N n → N (gcd (succ₁ n) zero)
gcd-S0-N {n} Nn = subst N (sym (gcd-S0 n)) (nsucc Nn)

------------------------------------------------------------------------------
-- gcd (succ₁ m) (succ₁ n) when succ₁ m > succ₁ n is total.
gcd-S>S-N : ∀ {m n} → N m → N n →
            N (gcd (succ₁ m ∸ succ₁ n) (succ₁ n)) →
            succ₁ m > succ₁ n →
            N (gcd (succ₁ m) (succ₁ n))
gcd-S>S-N {m} {n} Nm Nn ih Sm>Sn = subst N (sym (gcd-S>S m n Sm>Sn)) ih

------------------------------------------------------------------------------
-- gcd (succ₁ m) (succ₁ n) when succ₁ m ≯ succ₁ n is total.
gcd-S≯S-N : ∀ {m n} → N m → N n →
            N (gcd (succ₁ m) (succ₁ n ∸ succ₁ m)) →
            succ₁ m ≯ succ₁ n →
            N (gcd (succ₁ m) (succ₁ n))
gcd-S≯S-N {m} {n} Nm Nn ih Sm≯Sn = subst N (sym (gcd-S≯S m n Sm≯Sn)) ih

------------------------------------------------------------------------------
-- gcd m n when m > n is total.
gcd-x>y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → Lexi o p m n → x≢0≢y o p → N (gcd o p)) →
  m > n →
  x≢0≢y m n →
  N (gcd m n)
gcd-x>y-N nzero          Nn             _  0>n   _ = ⊥-elim (0>x→⊥ Nn 0>n)
gcd-x>y-N (nsucc Nm)     nzero          _  _     _ = gcd-S0-N Nm
gcd-x>y-N (nsucc {m} Nm) (nsucc {n} Nn) ah Sm>Sn _ =
  gcd-S>S-N Nm Nn ih Sm>Sn
  where
  -- Inductive hypothesis.
  ih : N (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))
  ih = ah {succ₁ m ∸ succ₁ n}
          {succ₁ n}
          (∸-N (nsucc Nm) (nsucc Nn))
          (nsucc Nn)
          ([Sx∸Sy,Sy]<[Sx,Sy] Nm Nn)
          (λ p → ⊥-elim (S≢0 (∧-proj₂ p)))

------------------------------------------------------------------------------
-- gcd m n when m ≯ n is total.
gcd-x≯y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → Lexi o p m n → x≢0≢y o p → N (gcd o p)) →
  m ≯ n →
  x≢0≢y m n →
  N (gcd m n)
gcd-x≯y-N nzero          nzero          _  _     h = ⊥-elim (h (refl , refl))
gcd-x≯y-N nzero          (nsucc Nn)     _  _     _ = gcd-0S-N Nn
gcd-x≯y-N (nsucc _)      nzero          _  Sm≯0  _ = ⊥-elim (S≯0→⊥ Sm≯0)
gcd-x≯y-N (nsucc {m} Nm) (nsucc {n} Nn) ah Sm≯Sn _ = gcd-S≯S-N Nm Nn ih Sm≯Sn
  where
  -- Inductive hypothesis.
  ih : N (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))
  ih = ah {succ₁ m}
          {succ₁ n ∸ succ₁ m}
          (nsucc Nm)
          (∸-N (nsucc Nn) (nsucc Nm))
          ([Sx,Sy∸Sx]<[Sx,Sy] Nm Nn)
          (λ p → ⊥-elim (S≢0 (∧-proj₁ p)))

------------------------------------------------------------------------------
-- gcd m n when m ≢ 0 and n ≢ 0 is total.
gcd-N : ∀ {m n} → N m → N n → x≢0≢y m n → N (gcd m n)
gcd-N = Lexi-wfind A h
  where
  A : D → D → Set
  A i j = x≢0≢y i j → N (gcd i j)

  h : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → Lexi k l i j → A k l) →
      A i j
  h Ni Nj ah = case (gcd-x>y-N Ni Nj ah) (gcd-x≯y-N Ni Nj ah) (x>y∨x≯y Ni Nj)
