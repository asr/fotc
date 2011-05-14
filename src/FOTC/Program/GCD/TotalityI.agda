------------------------------------------------------------------------------
-- Totality properties of the gcd
------------------------------------------------------------------------------

module FOTC.Program.GCD.TotalityI where

open import FOTC.Base
open import FOTC.Base.Properties

open import Common.Function

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI

open import FOTC.Program.GCD.Definitions
open import FOTC.Program.GCD.GCD

------------------------------------------------------------------------------
-- gcd 0 (succ n) is total.
gcd-0S-N : ∀ {n} → N n → N (gcd zero (succ n))
gcd-0S-N {n} Nn = subst N (sym $ gcd-0S n) (sN Nn)

------------------------------------------------------------------------------
-- gcd (succ n) 0 is total.
gcd-S0-N : ∀ {n} → N n → N (gcd (succ n) zero)
gcd-S0-N {n} Nn = subst N (sym $ gcd-S0 n) (sN Nn)

------------------------------------------------------------------------------
-- gcd (succ m) (succ n) when succ m > succ n is total.
gcd-S>S-N : ∀ {m n} → N m → N n →
            N (gcd (succ m ∸ succ n) (succ n)) →
            GT (succ m) (succ n) →
            N (gcd (succ m) (succ n))
gcd-S>S-N {m} {n} Nm Nn ih Sm>Sn = subst N (sym $ gcd-S>S m n Sm>Sn) ih

------------------------------------------------------------------------------
-- gcd (succ m) (succ n) when succ m ≯ succ n is total.
gcd-S≯S-N : ∀ {m n} → N m → N n →
            N (gcd (succ m) (succ n ∸ succ m)) →
            NGT (succ m) (succ n) →
            N (gcd (succ m) (succ n))
gcd-S≯S-N {m} {n} Nm Nn ih Sm≯Sn = subst N (sym $ gcd-S≯S m n Sm≯Sn) ih

------------------------------------------------------------------------------
-- gcd m n when m > n is total.
gcd-x>y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → x≠0≠y o p → N (gcd o p)) →
  GT m n →
  x≠0≠y m n →
  N (gcd m n)
gcd-x>y-N zN zN _ _ ¬0≡0∧0≡0   = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x>y-N zN (sN Nn) _ 0>Sn _  = ⊥-elim $ 0>x→⊥ (sN Nn) 0>Sn
gcd-x>y-N (sN Nm) zN  _  _ _   = gcd-S0-N Nm
gcd-x>y-N (sN {m} Nm) (sN {n} Nn) accH Sm>Sn _ =
  gcd-S>S-N Nm Nn ih Sm>Sn
  where
    -- Inductive hypothesis.
    ih : N (gcd (succ m ∸ succ n) (succ n))
    ih = accH {succ m ∸ succ n}
              {succ n}
              (∸-N (sN Nm) (sN Nn))
              (sN Nn)
              ([Sx∸Sy,Sy]<[Sx,Sy] Nm Nn)
              (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₂ p)

------------------------------------------------------------------------------
-- gcd m n when m ≯ n is total.
gcd-x≯y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → x≠0≠y o p → N (gcd o p)) →
  NGT m n →
  x≠0≠y m n →
  N (gcd m n)
gcd-x≯y-N zN zN _ _  ¬0≡0∧0≡0 = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x≯y-N zN (sN Nn) _ _ _  = gcd-0S-N Nn
gcd-x≯y-N (sN {m} Nm) zN _ Sm≯0 _  =
  ⊥-elim (true≠false (trans (sym (<-0S m)) Sm≯0))
gcd-x≯y-N (sN {m} Nm) (sN {n} Nn) accH Sm≯Sn _ =
  gcd-S≯S-N Nm Nn ih Sm≯Sn
  where
    -- Inductive hypothesis.
    ih : N (gcd (succ m) (succ n ∸ succ m))
    ih = accH {succ m}
              {succ n ∸ succ m}
              (sN Nm)
              (∸-N (sN Nn) (sN Nm))
              ([Sx,Sy∸Sx]<[Sx,Sy] Nm Nn)
              (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₁ p)

------------------------------------------------------------------------------
-- gcd m n when m ≠ 0 and n ≠ 0 is total.
gcd-N : ∀ {m n} → N m → N n → x≠0≠y m n → N (gcd m n)
gcd-N = wfInd-LT₂ P istep
  where
    P : D → D → Set
    P i j = x≠0≠y i j → N (gcd i j)

    istep : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → LT₂ k l i j → P k l) →
            P i j
    istep Ni Nj accH =
      [ gcd-x>y-N Ni Nj accH
      , gcd-x≯y-N Ni Nj accH
      ] (x>y∨x≯y Ni Nj)
