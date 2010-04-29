------------------------------------------------------------------------------
-- The gcd is N (using equational reasoning)
------------------------------------------------------------------------------

-- We prove that 'gcd-N : ... → N (gcd m n).

module Examples.GCD.Properties.IsN-ER where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.GCD

open import LTC.Data.N
open import LTC.Data.N.Postulates using ( wf₂-indN )
open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.PropertiesER
open import LTC.Relation.Equalities.PropertiesER
open import LTC.Relation.Inequalities
open import LTC.Relation.Inequalities.Postulates
  using ( Sx>Sy→[Sx-Sy,Sy]<₂[Sx,Sy] ; Sx≤Sy→[Sx,Sy-Sx]<₂[Sx,Sy] )
open import LTC.Relation.Inequalities.PropertiesER

open import MyStdLib.Data.Sum
open import MyStdLib.Function

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
  ({m' n' : D} → N m' → N n' → LT₂ (m' , n') (m , n) →
       ¬ ((m' ≡ zero) ∧ (n' ≡ zero)) → N (gcd m' n')) →
  GT m n →
  ¬ ((m ≡ zero) ∧ (n ≡ zero)) → N (gcd m n)
gcd-x>y-N zN zN _ _ ¬0≡0∧0≡0  = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x>y-N zN (sN Nn) _ 0>Sn _ = ⊥-elim (¬0>x (sN Nn) 0>Sn)
gcd-x>y-N (sN Nm) zN _ _ _    = gcd-S0-N Nm
gcd-x>y-N (sN {m} Nm) (sN {n} Nn) allAcc Sm>Sn _ =
  gcd-S>S-N Nm Nn ih Sm>Sn
  where
    -- Inductive hypothesis
    ih : N (gcd (succ m - succ n) (succ n))
    ih = allAcc (minus-N (sN Nm) (sN Nn))
                (sN Nn)
                (Sx>Sy→[Sx-Sy,Sy]<₂[Sx,Sy] Nm Nn Sm>Sn)
                (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₂ p)

---------------------------------------------------------------------------
-- The 'gcd m n' when 'm ≤ n' is N.

-- N.B. If '≤' were an inductive data type, we would use the absurd pattern
-- to prove the third case.

gcd-x≤y-N :
  {m n : D} → N m → N n →
  ({m' n' : D} → N m' → N n' → LT₂ (m' , n') (m , n) →
       ¬ ((m' ≡ zero) ∧ (n' ≡ zero)) → N (gcd m' n')) →
  LE m n →
  ¬ ((m ≡ zero) ∧ (n ≡ zero)) → N (gcd m n)

gcd-x≤y-N zN zN _ _ ¬0≡0∧0≡0  = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x≤y-N zN (sN Nn) _ _ _    = gcd-0S-N Nn
gcd-x≤y-N (sN _ ) zN _ Sm≤0 _ = ⊥-elim $ ¬S≤0 Sm≤0
gcd-x≤y-N (sN {m} Nm) (sN {n} Nn) allAcc Sm≤Sn _ =
  gcd-S≤S-N Nm Nn ih Sm≤Sn
  where
    -- Inductive hypothesis
    ih : N (gcd (succ m) (succ n - succ m))
    ih = allAcc (sN Nm)
                (minus-N (sN Nn)  (sN Nm ))
                (Sx≤Sy→[Sx,Sy-Sx]<₂[Sx,Sy] Nm Nn Sm≤Sn)
                (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₁ p)

---------------------------------------------------------------------------
-- The 'gcd' is N.

gcd-N : {m n : D} → N m → N n → ¬ ((m ≡ zero) ∧ (n ≡ zero)) →
        N (gcd m n)
gcd-N = wf₂-indN P istep
  where
    P : D → D → Set
    P i j = ¬ ((i ≡ zero) ∧ (j ≡ zero)) → N (gcd i j )

    istep :
      {i j : D} → N i → N j →
      ({i' j' : D} → N i' → N j' → LT₂ (i' , j') (i , j) → P i' j') →
      P i j
    istep Ni Nj allAcc =
      [ gcd-x>y-N Ni Nj allAcc , gcd-x≤y-N Ni Nj allAcc ] (x>y∨x≤y Ni Nj)
