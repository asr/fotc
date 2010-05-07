------------------------------------------------------------------------------
-- The gcd is divisible by any common divisor
------------------------------------------------------------------------------

module Examples.GCD.IsDivisible where

open import LTC.Minimal

open import Examples.GCD.Equations
open import Examples.GCD.IsCommonDivisor
open import Examples.GCD.Types

open import LTC.Data.N
open import LTC.Data.N.Induction.Lexicographic
open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.Properties
open import LTC.Relation.Divisibility
open import LTC.Relation.Divisibility.Properties
open import LTC.Relation.Equalities.Properties
open import LTC.Relation.Inequalities
open import Postulates
  using ( Sx>Sy→[Sx-Sy,Sy]<[Sx,Sy] ; Sx≤Sy→[Sx,Sy-Sx]<[Sx,Sy] )
open import LTC.Relation.Inequalities.Properties

open import MyStdLib.Function
import MyStdLib.Induction.Lexicographic
open module IsDivisible-LT₂ = MyStdLib.Induction.Lexicographic LT LT

------------------------------------------------------------------------------
-- Divisible for any common divisor.

Divisible : D → D → D → Set
Divisible a b gcd = (c : D) → N c → CD a b c → c ∣ gcd
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
  {mn : D × D} → N₂ mn →
  ((op : D × D ) → LT₂ op mn →
       N₂ op →
       ¬x≡0∧y≡0 (×-proj₁ op) (×-proj₂ op) →
       Divisible (×-proj₁ op) (×-proj₂ op) (gcd (×-proj₁ op) (×-proj₂ op))) →
  GT (×-proj₁ mn) (×-proj₂ mn) →
  ¬x≡0∧y≡0 (×-proj₁ mn) (×-proj₂ mn) →
  Divisible (×-proj₁ mn) (×-proj₂ mn) (gcd (×-proj₁ mn) (×-proj₂ mn))

gcd-x>y-Divisible (zN , zN )_ _ ¬0≡0∧0≡0 _ _  = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x>y-Divisible (zN , sN Nn ) _ 0>Sn _ _ _ = ⊥-elim (¬0>x (sN Nn) 0>Sn)
gcd-x>y-Divisible (sN Nm , zN ) _ _ _  c Nc  = gcd-S0-Divisible Nm c Nc
gcd-x>y-Divisible (sN {m} Nm , sN {n} Nn ) allAcc Sm>Sn _ c Nc =
  gcd-S>S-Divisible Nm Nn ih Sm>Sn c Nc
  where -- Inductive hypothesis.
    ih : Divisible (succ m - succ n) (succ n) (gcd (succ m - succ n) (succ n))
    ih = allAcc (succ m - succ n , succ n)
                (Sx>Sy→[Sx-Sy,Sy]<[Sx,Sy] Nm Nn Sm>Sn)
                (minus-N (sN Nm) (sN Nn) , sN Nn)
                (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₂ p )

---------------------------------------------------------------------------
-- The 'gcd m n' when 'm ≤ n' is Divisible.

-- N.B. If '≤' were an inductive data type, we would use the absurd pattern
-- to prove the third case.

gcd-x≤y-Divisible :
  {mn : D × D} → N₂ mn →
  ((op : D × D ) → LT₂ op mn →
       N₂ op →
       ¬x≡0∧y≡0 (×-proj₁ op) (×-proj₂ op) →
       Divisible (×-proj₁ op) (×-proj₂ op) (gcd (×-proj₁ op) (×-proj₂ op))) →
  LE (×-proj₁ mn) (×-proj₂ mn) →
  ¬x≡0∧y≡0 (×-proj₁ mn) (×-proj₂ mn) →
  Divisible (×-proj₁ mn) (×-proj₂ mn) (gcd (×-proj₁ mn) (×-proj₂ mn))

gcd-x≤y-Divisible (zN , zN ) _ _ ¬0≡0∧0≡0 _ _ = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x≤y-Divisible (zN , sN Nn ) _ _  _  c Nc  = gcd-0S-Divisible Nn c Nc
gcd-x≤y-Divisible (sN Nm , zN ) _ Sm≤0 _ _ _  = ⊥-elim $ ¬S≤0 Sm≤0
gcd-x≤y-Divisible (sN {m} Nm , sN {n} Nn ) allAcc Sm≤Sn _ c Nc =
  gcd-S≤S-Divisible Nm Nn ih Sm≤Sn c Nc
  where -- Inductive hypothesis.
    ih : Divisible (succ m) (succ n - succ m) (gcd (succ m) (succ n - succ m))
    ih = allAcc (succ m , succ n - succ m)
                (Sx≤Sy→[Sx,Sy-Sx]<[Sx,Sy] Nm Nn Sm≤Sn)
                (sN Nm , minus-N (sN Nn) (sN Nm ))
                (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₁ p )

---------------------------------------------------------------------------
-- The gcd is Divisible.

gcd-Divisible : {mn : D × D } → N₂ mn →
         ¬x≡0∧y≡0 (×-proj₁ mn) (×-proj₂ mn) →
         Divisible (×-proj₁ mn) (×-proj₂ mn) (gcd (×-proj₁ mn) (×-proj₂ mn))
gcd-Divisible = wellFoundedInd-N₂ P istep
  where
    P : D × D → Set
    P ij = ¬x≡0∧y≡0 i j → Divisible i j  (gcd i j )
      where i : D
            i = ×-proj₁ ij
            j : D
            j = ×-proj₂ ij

    istep :
      (ij : D × D) → ((kl : D × D) → LT₂ kl ij → N₂ kl → P kl) → N₂ ij → P ij
    istep ij allAcc N₂ij =
      [ gcd-x>y-Divisible N₂ij allAcc
      , gcd-x≤y-Divisible N₂ij allAcc
      ] (x>y∨x≤y (N₂-proj₁ N₂ij) (N₂-proj₂ N₂ij))
