------------------------------------------------------------------------------
-- The gcd is divisible by any common divisor
------------------------------------------------------------------------------

module Examples.GCD.Properties.IsDivisible where

open import LTC.Minimal

open import Examples.GCD
open import Examples.GCD.Properties.IsCommonDivisor

open import LTC.Data.N
open import LTC.Data.N.Postulates
open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.Properties
open import LTC.Relation.Divisibility
open import LTC.Relation.Divisibility.Postulates
open import LTC.Relation.Divisibility.Properties
open import LTC.Relation.Equalities.Properties
open import LTC.Relation.Inequalities
open import LTC.Relation.Inequalities.Postulates
open import LTC.Relation.Inequalities.Properties

open import MyStdLib.Function
open import MyStdLib.Data.Sum

------------------------------------------------------------------------------
-- Divisible for any common divisor.

Divisible : D → D → D → Set
Divisible a b g = (c : D) → N c → CD a b c → c ∣ g
{-# ATP definition Divisible #-}

---------------------------------------------------------------------------
-- The gcd is divisible by any common divisor
---------------------------------------------------------------------------

-- We will prove that 'gcd-Divisible : ... → Divisible m n (gcd m n).

---------------------------------------------------------------------------
-- The 'gcd 0 (succ n)' is Divisible.

postulate
  gcd-0S-Divisible : {n : D} → N n →
                     Divisible zero (succ n) (gcd zero (succ n))
{-# ATP prove gcd-0S-Divisible #-}

postulate
  gcd-S0-Divisible : {n : D} → N n →
                     Divisible (succ n) zero (gcd (succ n) zero)
{-# ATP prove gcd-S0-Divisible #-}

---------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m > succ n' is Divisible.

-- For the proof using the ATP we added the auxliar hypothesis
-- c | succ m → c | succ c → c | succ m - succ n.
postulate
  gcd-S>S-Divisible-ah :
    {m n : D} → N m → N n →
    (Divisible (succ m - succ n) (succ n) (gcd (succ m - succ n) (succ n))) →
    GT (succ m) (succ n) →
    (c : D) → N c → CD (succ m) (succ n) c →
    (c ∣ succ m - succ n) →
    c ∣ gcd (succ m) (succ n)
{-# ATP prove gcd-S>S-Divisible-ah #-}

gcd-S>S-Divisible :
  {m n : D} → N m → N n →
  (Divisible (succ m - succ n) (succ n) (gcd (succ m - succ n) (succ n))) →
  GT (succ m) (succ n) →
  Divisible (succ m) (succ n) (gcd (succ m) (succ n))
gcd-S>S-Divisible {m} {n} Nm Nn acc Sm>Sn c Nc ( c∣Sm , c∣Sn) =
    gcd-S>S-Divisible-ah Nm Nn acc Sm>Sn c Nc (( c∣Sm , c∣Sn ))
                         (x∣y→x∣z→x∣y-z Nc (sN Nm) (sN Nn) c∣Sm c∣Sn)

---------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m ≤ succ n' is Divisible.

-- For the proof using the ATP we added the auxiliar hypothesis
-- c | succ n → c | succ m → c | succ n - succ m.
postulate
  gcd-S≤S-Divisible-ah :
    {m n : D} → N m → N n →
    (Divisible (succ m) (succ n - succ m) (gcd (succ m) (succ n - succ m))) →
    LE (succ m) (succ n) →
    (c : D) → N c → CD (succ m) (succ n) c →
    (c ∣ succ n - succ m) →
    c ∣ gcd (succ m) (succ n)
{-# ATP prove gcd-S≤S-Divisible-ah #-}

gcd-S≤S-Divisible :
  {m n : D} → N m → N n →
  (Divisible (succ m) (succ n - succ m) (gcd (succ m) (succ n - succ m))) →
  LE (succ m) (succ n) →
  Divisible (succ m) (succ n) (gcd (succ m) (succ n))
gcd-S≤S-Divisible {m} {n} Nm Nn acc Sm≤Sn c Nc ( c∣Sm , c∣Sn) =
    gcd-S≤S-Divisible-ah Nm Nn acc Sm≤Sn c Nc (( c∣Sm , c∣Sn ))
                         (x∣y→x∣z→x∣y-z Nc (sN Nn) (sN Nm) c∣Sn c∣Sm)

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
