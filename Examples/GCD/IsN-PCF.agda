------------------------------------------------------------------------------
-- The gcd is N
------------------------------------------------------------------------------

-- We prove that 'gcd-N : ... → N (gcd m n).

module Examples.GCD.IsN-PCF where

open import LTC.Minimal

open import Examples.GCD.EquationsPCF
open import Examples.GCD.Types

open import LTC.Data.N
open import LTC.Data.N.Induction.LexicographicPCF
open import LTC.Function.ArithmeticPCF
open import LTC.Function.Arithmetic.PropertiesPCF
open import LTC.Relation.Equalities.Properties
open import LTC.Relation.InequalitiesPCF
open import LTC.Relation.Inequalities.PropertiesPCF

open import MyStdLib.Function

------------------------------------------------------------------------------
-- The 'gcd 0 (succ n)' is N.
postulate
  gcd-0S-N : {n : D} → N n → N (gcd zero (succ n))
{-# ATP prove gcd-0S-N sN #-}

------------------------------------------------------------------------------
-- The 'gcd (succ n) 0' is N.

postulate
  gcd-S0-N : {n : D} → N n → N (gcd (succ n) zero)
{-# ATP prove gcd-S0-N sN #-}

------------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m > succ n' is N.

postulate
  gcd-S>S-N : {m n : D} → N m → N n →
              N (gcd (succ m - succ n) (succ n)) →
              GT (succ m) (succ n) →
              N (gcd (succ m) (succ n))
{-# ATP prove gcd-S>S-N #-}

------------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m ≤ succ n' is N.

postulate
  gcd-S≤S-N : {m n : D} → N m → N n →
              N (gcd (succ m) (succ n - succ m)) →
              LE (succ m) (succ n) →
              N (gcd (succ m) (succ n))
{-# ATP prove gcd-S≤S-N #-}

---------------------------------------------------------------------------
-- The 'gcd m n' when 'm > n' is N.

-- N.B. If '>' were an inductive data type, we would use the absurd pattern
-- to prove the second case.

gcd-x>y-N :
  {m n : D} → N m → N n →
  ({o p : D} → N o → N p → LT₂ o p m n → ¬x≡0∧y≡0 o p → N (gcd o p)) →
  GT m n →
  ¬x≡0∧y≡0 m n →
  N (gcd m n)
gcd-x>y-N zN zN _ _ ¬0≡0∧0≡0   = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x>y-N zN (sN Nn) _ 0>Sn _  = ⊥-elim (¬0>x (sN Nn) 0>Sn)
gcd-x>y-N (sN Nm) zN  _  _ _   = gcd-S0-N Nm
gcd-x>y-N (sN {m} Nm) (sN {n} Nn) accH Sm>Sn _ =
  gcd-S>S-N Nm Nn ih Sm>Sn
  where
    -- Inductive hypothesis
    ih : N (gcd (succ m - succ n) (succ n))
    ih = accH {succ m - succ n}
              {succ n}
              (minus-N (sN Nm) (sN Nn))
              (sN Nn)
              ([Sx-Sy,Sy]<[Sx,Sy] Nm Nn)
              (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₂ p)

---------------------------------------------------------------------------
-- The 'gcd m n' when 'm ≤ n' is N.

-- N.B. If '≤' were an inductive data type, we would use the absurd pattern
-- to prove the third case.

gcd-x≤y-N :
  {m n : D} → N m → N n →
  ({o p : D} → N o → N p → LT₂ o p m n → ¬x≡0∧y≡0 o p → N (gcd o p)) →
  LE m n →
  ¬x≡0∧y≡0 m n →
  N (gcd m n)
gcd-x≤y-N zN zN _ _  ¬0≡0∧0≡0 = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x≤y-N zN (sN Nn) _ _ _      = gcd-0S-N Nn
gcd-x≤y-N (sN _) zN _ Sm≤0  _  = ⊥-elim $ ¬S≤0 Sm≤0
gcd-x≤y-N (sN {m} Nm) (sN {n} Nn) accH Sm≤Sn _ =
  gcd-S≤S-N Nm Nn ih Sm≤Sn
  where
    -- Inductive hypothesis
    ih : N (gcd (succ m) (succ n - succ m))
    ih = accH {succ m}
              {succ n - succ m}
              (sN Nm)
              (minus-N (sN Nn) (sN Nm))
              ([Sx,Sy-Sx]<[Sx,Sy] Nm Nn)
              (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₁ p)

---------------------------------------------------------------------------
-- The 'gcd' is N.

gcd-N : {m n : D } → N m → N n → ¬x≡0∧y≡0 m n → N (gcd m n)
gcd-N = wfIndN-LT₂ P istep
  where
    P : D → D → Set
    P i j = ¬x≡0∧y≡0 i j → N (gcd i j )

    istep :
      {i j : D} → N i → N j →
      ({k l : D} → N k → N l → LT₂ k l i j → P k l) →
      P i j
    istep Ni Nj accH =
      [ gcd-x>y-N Ni Nj accH
      , gcd-x≤y-N Ni Nj accH
      ] (x>y∨x≤y Ni Nj)
