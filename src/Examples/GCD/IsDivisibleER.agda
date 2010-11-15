------------------------------------------------------------------------------
-- The gcd is divisible by any common divisor (using equational reasoning)
------------------------------------------------------------------------------

module Examples.GCD.IsDivisibleER where

open import LTC.Base
open import LTC.Base.Properties using ( ¬S≡0 )
open import LTC.BaseER using ( subst )

open import Examples.GCD.GCD
  using ( ¬x≡0∧y≡0 ; gcd ; gcd-0S ; gcd-S0 ; gcd-S>S ; gcd-S≤S )
open import Examples.GCD.IsCommonDivisorER using ( CD )

open import Lib.Function using ( _$_ )

open import LTC.Data.Nat
  using ( _-_
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC.Data.Nat.Divisibility using ( _∣_ )
open import LTC.Data.Nat.Divisibility.PropertiesER using ( x∣y→x∣z→x∣y-z )
open import LTC.Data.Nat.Induction.Lexicographic using ( wfIndN-LT₂ )
open import LTC.Data.Nat.Inequalities using ( GT ; LE ; LT₂ )
open import LTC.Data.Nat.Inequalities.PropertiesER
  using ( ¬0>x
        ; ¬S≤0
        ; [Sx-Sy,Sy]<[Sx,Sy]
        ; [Sx,Sy-Sx]<[Sx,Sy]
        ; x>y∨x≤y
        )
open import LTC.Data.Nat.PropertiesER using ( minus-N )

------------------------------------------------------------------------------
-- Divisible for any common divisor.
Divisible : D → D → D → Set
Divisible a b gcd = (c : D) → N c → CD a b c → c ∣ gcd

------------------------------------------------------------------------------
-- The 'gcd 0 (succ n)' is Divisible.
gcd-0S-Divisible : {n : D} → N n → Divisible zero (succ n) (gcd zero (succ n))
gcd-0S-Divisible {n} _ c _ ( c∣0 , c∣Sn ) =
  subst (λ x → c ∣ x) (sym $ gcd-0S n) c∣Sn

------------------------------------------------------------------------------
-- The 'gcd (succ n) 0' is Divisible.
gcd-S0-Divisible : {n : D} → N n → Divisible (succ n) zero (gcd (succ n) zero)
gcd-S0-Divisible {n} _ c _ ( c∣Sn , c∣0) =
  subst (λ x → c ∣ x) (sym $ gcd-S0 n) c∣Sn

------------------------------------------------------------------------------
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
 subst (λ x → c ∣ x)
       (sym $ gcd-S>S m n Sm>Sn)
       (acc c Nc ( c|Sm-Sn , c∣Sn ))
 where
   c|Sm-Sn : c ∣ succ m - succ n
   c|Sm-Sn = x∣y→x∣z→x∣y-z Nc (sN Nm) (sN Nn) c∣Sm c∣Sn

------------------------------------------------------------------------------
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

  subst (λ x → c ∣ x)
        (sym $ gcd-S≤S m n Sm≤Sn)
        (acc c Nc ( c∣Sm , c|Sn-Sm ))
  where
    c|Sn-Sm : c ∣ succ n - succ m
    c|Sn-Sm = x∣y→x∣z→x∣y-z Nc (sN Nn) (sN Nm) c∣Sn c∣Sm

------------------------------------------------------------------------------
-- The 'gcd m n' when 'm > n' is Divisible.
-- N.B. If '>' were an inductive data type, we would use the absurd pattern
-- to prove the second case.
gcd-x>y-Divisible :
  {m n : D} → N m → N n →
  ({o p : D} → N o → N p → LT₂ o p m n → ¬x≡0∧y≡0 o p →
               Divisible o p (gcd o p)) →
  GT m n →
  ¬x≡0∧y≡0 m n →
  Divisible m n (gcd m n)
gcd-x>y-Divisible zN zN _ _ ¬0≡0∧0≡0 _ _  = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x>y-Divisible zN (sN Nn) _ 0>Sn _ _ _ = ⊥-elim $ ¬0>x (sN Nn) 0>Sn
gcd-x>y-Divisible (sN Nm) zN _ _ _  c Nc  = gcd-S0-Divisible Nm c Nc
gcd-x>y-Divisible (sN {m} Nm) (sN {n} Nn) accH Sm>Sn _ c Nc =
  gcd-S>S-Divisible Nm Nn ih Sm>Sn c Nc
  where
    -- Inductive hypothesis.
    ih : Divisible (succ m - succ n) (succ n) (gcd (succ m - succ n) (succ n))
    ih = accH {succ m - succ n}
              {succ n}
              (minus-N (sN Nm) (sN Nn))
              (sN Nn)
              ([Sx-Sy,Sy]<[Sx,Sy] Nm Nn)
              (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₂ p)

------------------------------------------------------------------------------
-- The 'gcd m n' when 'm ≤ n' is Divisible.
-- N.B. If '≤' were an inductive data type, we would use the absurd pattern
-- to prove the third case.
gcd-x≤y-Divisible :
  {m n : D} → N m → N n →
  ({o p : D} → N o → N p → LT₂ o p m n → ¬x≡0∧y≡0 o p →
               Divisible o p (gcd o p)) →
  LE m n →
  ¬x≡0∧y≡0 m n →
  Divisible m n (gcd m n)
gcd-x≤y-Divisible zN zN _ _ ¬0≡0∧0≡0 _ _   = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x≤y-Divisible zN (sN Nn) _ _  _  c Nc  = gcd-0S-Divisible Nn c Nc
gcd-x≤y-Divisible (sN Nm) zN _ Sm≤0 _ _ _  = ⊥-elim $ ¬S≤0 Nm Sm≤0
gcd-x≤y-Divisible (sN {m} Nm) (sN {n} Nn) accH Sm≤Sn _ c Nc =
  gcd-S≤S-Divisible Nm Nn ih Sm≤Sn c Nc
  where
    -- Inductive hypothesis.
    ih : Divisible (succ m) (succ n - succ m) (gcd (succ m) (succ n - succ m))
    ih = accH {succ m}
              {succ n - succ m}
              (sN Nm)
              (minus-N (sN Nn) (sN Nm))
              ([Sx,Sy-Sx]<[Sx,Sy] Nm Nn)
              (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₁ p)

------------------------------------------------------------------------------
-- The gcd is Divisible.
gcd-Divisible : {m n : D} → N m → N n → ¬x≡0∧y≡0 m n → Divisible m n (gcd m n)
gcd-Divisible = wfIndN-LT₂ P istep
  where
    P : D → D → Set
    P i j = ¬x≡0∧y≡0 i j → Divisible i j (gcd i j)

    istep :
      {i j : D} → N i → N j →
      ({k l : D} → N k → N l → LT₂ k l i j → P k l) →
      P i j
    istep Ni Nj accH =
      [ gcd-x>y-Divisible Ni Nj accH
      , gcd-x≤y-Divisible Ni Nj accH
      ] (x>y∨x≤y Ni Nj)
