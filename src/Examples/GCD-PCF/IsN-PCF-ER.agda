------------------------------------------------------------------------------
-- The gcd is N (using equational reasoning)
------------------------------------------------------------------------------

module Examples.GCD-PCF.IsN-PCF-ER where

open import LTC.Base
open import LTC.Base.Properties using ( ¬S≡0 )
open import LTC.BaseER using ( subst )

open import Examples.GCD-PCF.GCD-PCF using ( ¬x≡0∧y≡0 ; gcd )
open import Examples.GCD-PCF.EquationsPCF
  using ( gcd-0S ; gcd-S0 ; gcd-S>S ; gcd-S≤S )

open import Lib.Function using ( _$_ )

open import LTC-PCF.DataPCF.NatPCF
  using ( _-_
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.DataPCF.NatPCF.InductionPCF.LexicographicPCF
  using ( wfIndN-LT₂)
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF using ( GT ; LE ; LT₂ )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF.PropertiesPCF-ER
  using ( ¬0>x
        ; ¬S≤0
        ; x>y∨x≤y
        ; [Sx-Sy,Sy]<[Sx,Sy]
        ; [Sx,Sy-Sx]<[Sx,Sy]
        )
open import LTC-PCF.DataPCF.NatPCF.PropertiesPCF-ER using ( minus-N )

------------------------------------------------------------------------------
-- The 'gcd 0 (succ n)' is N.
gcd-0S-N : {n : D} → N n → N (gcd zero (succ n))
gcd-0S-N {n} Nn = subst N (sym (gcd-0S n)) (sN Nn)

---------------------------------------------------------------------------
-- The 'gcd (succ n) 0' is N.
gcd-S0-N : {n : D} → N n → N (gcd (succ n) zero)
gcd-S0-N {n} Nn = subst N (sym $ gcd-S0 n) (sN Nn)

---------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m > succ n' is N.
gcd-S>S-N : {m n : D} → N m → N n →
             N (gcd (succ m - succ n) (succ n)) →
             GT (succ m) (succ n) →
             N (gcd (succ m) (succ n))
gcd-S>S-N {m} {n} Nm Nn ih Sm>Sn = subst N (sym $ gcd-S>S m n Sm>Sn) ih

---------------------------------------------------------------------------

-- The 'gcd (succ m) (succ n)' when 'succ m ≤ succ n' is N.
gcd-S≤S-N : {m n : D} → N m → N n →
            N (gcd (succ m) (succ n - succ m)) →
            LE (succ m) (succ n) →
            N (gcd (succ m) (succ n))
gcd-S≤S-N {m} {n} Nm Nn ih Sm≤Sn = subst N (sym $ gcd-S≤S m n Sm≤Sn) ih

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
    -- Inductive hypothesis.
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
gcd-x≤y-N (sN Nm) zN _ Sm≤0  _  = ⊥-elim $ ¬S≤0 Nm Sm≤0
gcd-x≤y-N (sN {m} Nm) (sN {n} Nn) accH Sm≤Sn _ =
  gcd-S≤S-N Nm Nn ih Sm≤Sn
  where
    -- Inductive hypothesis.
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
    P i j = ¬x≡0∧y≡0 i j → N (gcd i j)

    istep :
      {i j : D} → N i → N j →
      ({k l : D} → N k → N l → LT₂ k l i j → P k l) →
      P i j
    istep Ni Nj accH =
      [ gcd-x>y-N Ni Nj accH
      , gcd-x≤y-N Ni Nj accH
      ] (x>y∨x≤y Ni Nj)
