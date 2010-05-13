------------------------------------------------------------------------------
-- The gcd is N (using equational reasoning)
------------------------------------------------------------------------------

-- We prove that 'gcd-N : ... → N (gcd m n).

module Examples.GCD.IsN-ER where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.GCD.Equations
open import Examples.GCD.Types

open import LTC.Data.N
open import LTC.Data.N.Induction.Lexicographic
open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.PropertiesER
open import LTC.Relation.Equalities.PropertiesER
open import LTC.Relation.Inequalities
open import LTC.Relation.Inequalities.Properties using ( [Sx-Sy,Sy]<[Sx,Sy] )
open import LTC.Relation.Inequalities.PropertiesER

open import MyStdLib.Function

open import Postulates using ( Sx≤Sy→[Sx,Sy-Sx]<[Sx,Sy] )

------------------------------------------------------------------------------
-- The 'gcd 0 (succ n)' is N.
gcd-0S-N : {n : D} → N n → N (gcd zero (succ n))
gcd-0S-N {n} Nn = subst (λ x → N x ) (sym (gcd-0S n)) (sN Nn)

---------------------------------------------------------------------------
-- The 'gcd (succ n) 0' is N.

gcd-S0-N : {n : D} → N n → N (gcd (succ n) zero)
gcd-S0-N {n} Nn = subst (λ x → N x ) (sym $ gcd-S0 n) (sN Nn)

---------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m > succ n' is N.

gcd-S>S-N : {m n : D} → N m → N n →
             N (gcd (succ m - succ n) (succ n)) →
             GT (succ m) (succ n) →
             N (gcd (succ m) (succ n))
gcd-S>S-N {m} {n} Nm Nn ih Sm>Sn =
  subst (λ x → N x ) (sym $ gcd-S>S m n Sm>Sn) ih

---------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m ≤ succ n' is N.

gcd-S≤S-N : {m n : D} → N m → N n →
            N (gcd (succ m) (succ n - succ m)) →
            LE (succ m) (succ n) →
            N (gcd (succ m) (succ n))
gcd-S≤S-N {m} {n} Nm Nn ih Sm≤Sn =
  subst (λ x → N x ) (sym $ gcd-S≤S m n Sm≤Sn ) ih

---------------------------------------------------------------------------
-- The 'gcd m n' when 'm > n' is N.

-- N.B. If '>' were an inductive data type, we would use the absurd pattern
-- to prove the second case.

gcd-x>y-N :
  {m n : D} → N m → N n →
  ({o p : D} → LT₂ o p m n → N o → N p → ¬x≡0∧y≡0 o p → N (gcd o p)) →
  GT m n →
  ¬x≡0∧y≡0 m n →
  N (gcd m n)
gcd-x>y-N zN zN _ _ ¬0≡0∧0≡0   = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x>y-N zN (sN Nn) _ 0>Sn _  = ⊥-elim (¬0>x (sN Nn) 0>Sn)
gcd-x>y-N (sN Nm) zN  _  _ _   = gcd-S0-N Nm
gcd-x>y-N (sN {m} Nm) (sN {n} Nn) allAcc Sm>Sn _ =
  gcd-S>S-N Nm Nn ih Sm>Sn
  where
    -- Inductive hypothesis
    ih : N (gcd (succ m - succ n) (succ n))
    ih = allAcc {succ m - succ n}
                {succ n}
                ([Sx-Sy,Sy]<[Sx,Sy] Nm Nn)
                (minus-N (sN Nm) (sN Nn))
                (sN Nn)
                (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₂ p)

---------------------------------------------------------------------------
-- The 'gcd m n' when 'm ≤ n' is N.

-- N.B. If '≤' were an inductive data type, we would use the absurd pattern
-- to prove the third case.

gcd-x≤y-N :
  {m n : D} → N m → N n →
  ({o p : D} → LT₂ o p m n → N o → N p → ¬x≡0∧y≡0 o p → N (gcd o p)) →
  LE m n →
  ¬x≡0∧y≡0 m n →
  N (gcd m n)
gcd-x≤y-N zN zN _ _  ¬0≡0∧0≡0 = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x≤y-N zN (sN Nn) _ _ _      = gcd-0S-N Nn
gcd-x≤y-N (sN _) zN _ Sm≤0  _  = ⊥-elim $ ¬S≤0 Sm≤0
gcd-x≤y-N (sN {m} Nm) (sN {n} Nn) allAcc Sm≤Sn _ =
  gcd-S≤S-N Nm Nn ih Sm≤Sn
  where
    -- Inductive hypothesis
    ih : N (gcd (succ m) (succ n - succ m))
    ih = allAcc {succ m}
                {succ n - succ m}
                (Sx≤Sy→[Sx,Sy-Sx]<[Sx,Sy] Nm Nn Sm≤Sn)
                (sN Nm)
                (minus-N (sN Nn) (sN Nm))
                (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₁ p)

---------------------------------------------------------------------------
-- The 'gcd' is N.

gcd-N : {m n : D } → N m → N n → ¬x≡0∧y≡0 m n → N (gcd m n)
gcd-N = wfInd-LT₂ P istep
  where
    P : D → D → Set
    P i j = ¬x≡0∧y≡0 i j → N (gcd i j )

    istep :
      {i j : D} → ({k l : D} → LT₂ k l i j → N k → N l → P k l) →
      N i → N j → P i j
    istep allAcc Ni Nj =
      [ gcd-x>y-N Ni Nj allAcc
      , gcd-x≤y-N Ni Nj allAcc
      ] (x>y∨x≤y Ni Nj)
