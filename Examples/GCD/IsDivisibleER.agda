------------------------------------------------------------------------------
-- The gcd is divisible by any common divisor (using equational reasoning)
------------------------------------------------------------------------------

module Examples.GCD.IsDivisibleER where

open import LTC.Minimal
open import LTC.MinimalER

open import Examples.GCD.Equations
open import Examples.GCD.IsCommonDivisorER

open import LTC.Data.N
open import LTC.Data.N.Postulates using ( wf₂-indN )
open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.PropertiesER
open import LTC.Relation.Divisibility
open import LTC.Relation.Divisibility.PropertiesER
open import LTC.Relation.Equalities.PropertiesER
open import LTC.Relation.Inequalities
open import LTC.Relation.Inequalities.Postulates
  using ( Sx>Sy→[Sx-Sy,Sy]<₂[Sx,Sy] ; Sx≤Sy→[Sx,Sy-Sx]<₂[Sx,Sy] )
open import LTC.Relation.Inequalities.PropertiesER

open import MyStdLib.Data.Sum
open import MyStdLib.Function

------------------------------------------------------------------------------
-- Divisible for any common divisor.

Divisible : D → D → D → Set
Divisible a b gcd = (c : D) → N c → CD a b c → c ∣ gcd

---------------------------------------------------------------------------
-- The gcd is divisible by any common divisor
---------------------------------------------------------------------------

-- We will prove that 'gcd-Divisible : ... → Divisible m n (gcd m n).

---------------------------------------------------------------------------
-- The 'gcd 0 (succ n)' is Divisible.

gcd-0S-Divisible : {n : D} → N n → Divisible zero (succ n) (gcd zero (succ n))
gcd-0S-Divisible {n} _ c _ ( c∣0 , c∣Sn ) =
  subst (λ x → c ∣ x ) (sym (gcd-0S n)) c∣Sn

---------------------------------------------------------------------------
-- The 'gcd (succ n) 0' is Divisible.

gcd-S0-Divisible : {n : D} → N n → Divisible (succ n) zero (gcd (succ n) zero)
gcd-S0-Divisible {n} _ c _ ( c∣Sn , c∣0) =
  subst (λ x → c ∣ x ) (sym (gcd-S0 n)) c∣Sn

---------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m > succ n' is Divisible.

gcd-S>S-Divisible :
  {m n : D} → N m → N n →
  (Divisible (succ m - succ n) (succ n) (gcd (succ m - succ n) (succ n))) →
  GT (succ m) (succ n) →
  Divisible (succ m) (succ n) (gcd (succ m) (succ n))
gcd-S>S-Divisible {m} {n} Nm Nn acc Sm>Sn c Nc ( c∣Sm , c∣Sn) =
{-
Proof:
   ----------------- (Hip.)
     c | m    c | n
   ---------------------- (Thm.)   -------- (Hip.)
       c | (m - n)                   c | n
     ------------------------------------------ (IH)
              c | gcd m (n - m)                          m > n
             --------------------------------------------------- (gcd def.)
                             c | gcd m n
-}
 subst (λ x → c ∣ x )
       (sym (gcd-S>S m n Sm>Sn))
       (acc c Nc ( c|Sm-Sn , c∣Sn ))
 where
   c|Sm-Sn : c ∣ succ m - succ n
   c|Sm-Sn = x∣y→x∣z→x∣y-z Nc (sN Nm ) (sN Nn ) c∣Sm c∣Sn

---------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m ≤ succ n' is Divisible.

gcd-S≤S-Divisible :
  {m n : D} → N m → N n →
  (Divisible (succ m) (succ n - succ m) (gcd (succ m) (succ n - succ m))) →
  LE (succ m) (succ n) →
  Divisible (succ m) (succ n) (gcd (succ m) (succ n))
gcd-S≤S-Divisible {m} {n} Nm Nn acc Sm≤Sn c Nc ( c∣Sm , c∣Sn) =
{-
Proof
                            ----------------- (Hip.)
                                c | m    c | n
        -------- (Hip.)       ---------------------- (Thm.)
         c | m                      c | n - m
     ------------------------------------------ (IH)
              c | gcd m (n - m)                          m ≤ n
             --------------------------------------------------- (gcd def.)
                             c | gcd m n
-}

  subst (λ x → c ∣ x )
        (sym (gcd-S≤S m n Sm≤Sn))
           (acc c Nc ( c∣Sm , c|Sn-Sm ))
  where
        c|Sn-Sm : c ∣ succ n - succ m
        c|Sn-Sm = x∣y→x∣z→x∣y-z Nc (sN Nn ) (sN Nm ) c∣Sn c∣Sm

---------------------------------------------------------------------------
-- The 'gcd m n' when 'm > n' is Divisible.

-- N.B. If '>' were an inductive data type, we would use the absurd pattern
-- to prove the second case.

gcd-x>y-Divisible :
  {m n : D} → N m → N n →
  ({m' n' : D} → N m' → N n' → LT₂ (m' , n') (m , n) →
    ¬ ((m' ≡ zero) ∧ (n' ≡ zero)) → Divisible m' n' (gcd m' n')) →
  GT m n →
  ¬ ((m ≡ zero) ∧ (n ≡ zero)) → Divisible m n (gcd m n)

gcd-x>y-Divisible zN zN _ _ ¬0≡0∧0≡0 _ _  = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x>y-Divisible zN (sN Nn) _ 0>Sn _ _ _ = ⊥-elim (¬0>x (sN Nn) 0>Sn)
gcd-x>y-Divisible (sN Nm) zN _ _ _  c Nc  = gcd-S0-Divisible Nm c Nc
gcd-x>y-Divisible (sN {m} Nm) (sN {n} Nn) allAcc Sm>Sn _ c Nc =
  gcd-S>S-Divisible Nm Nn ih Sm>Sn c Nc
  where -- Inductive hypothesis.
    ih : Divisible (succ m - succ n) (succ n) (gcd (succ m - succ n) (succ n))
    ih = allAcc (minus-N (sN Nm) (sN Nn))
                (sN Nn)
                (Sx>Sy→[Sx-Sy,Sy]<₂[Sx,Sy] Nm Nn Sm>Sn)
                (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₂ p )

---------------------------------------------------------------------------
-- The 'gcd m n' when 'm ≤ n' is Divisible.

-- N.B. If '≤' were an inductive data type, we would use the absurd pattern
-- to prove the third case.

gcd-x≤y-Divisible :
  {m n : D} → N m → N n →
  ({m' n' : D} → N m' → N n' → LT₂ (m' , n') (m , n) →
    ¬ ((m' ≡ zero) ∧ (n' ≡ zero)) → Divisible m' n' (gcd m' n')) →
  LE m n →
  ¬ ((m ≡ zero) ∧ (n ≡ zero)) → Divisible m n (gcd m n)

gcd-x≤y-Divisible zN zN _ _  ¬0≡0∧0≡0 _ _   = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x≤y-Divisible zN (sN Nn) _ _  _  c Nc   = gcd-0S-Divisible Nn c Nc
gcd-x≤y-Divisible (sN Nm) zN  _ Sm≤0 _ _ _  = ⊥-elim $ ¬S≤0 Sm≤0
gcd-x≤y-Divisible (sN {m} Nm) (sN {n} Nn) allAcc Sm≤Sn _ c Nc =
  gcd-S≤S-Divisible Nm Nn ih Sm≤Sn c Nc
  where -- Inductive hypothesis.
    ih : Divisible (succ m) (succ n - succ m) (gcd (succ m) (succ n - succ m))
    ih = allAcc (sN Nm)
                (minus-N (sN Nn)  (sN Nm ))
                (Sx≤Sy→[Sx,Sy-Sx]<₂[Sx,Sy] Nm Nn Sm≤Sn)
                (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₁ p )

---------------------------------------------------------------------------
-- The gcd is Divisible.

gcd-Divisible : {m n : D} → N m → N n → ¬ ((m ≡ zero) ∧ (n ≡ zero)) →
                Divisible m n (gcd m n)
gcd-Divisible = wf₂-indN P istep
  where
    P : D → D → Set
    P i j = ¬ ((i ≡ zero) ∧ (j ≡ zero)) → Divisible i j (gcd i j)

    istep :
      {i j : D} → N i → N j →
      ({i' j' : D} → N i' → N j' → LT₂ (i' , j') (i , j) → P i' j') →
      P i j
    istep Ni Nj allAcc =
      [ gcd-x>y-Divisible Ni Nj allAcc , gcd-x≤y-Divisible Ni Nj allAcc ]
      (x>y∨x≤y Ni Nj)
