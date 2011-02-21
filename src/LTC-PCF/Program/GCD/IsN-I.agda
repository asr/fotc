------------------------------------------------------------------------------
-- The gcd is N
------------------------------------------------------------------------------

module LTC-PCF.Program.GCD.IsN-I where

open import LTC-PCF.Base
open import FOTC.Base.Properties using ( ¬S≡0 )

open import Common.Function using ( _$_ )

open import LTC-PCF.Data.Nat
  using ( _∸_
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.Data.Nat.Induction.LexicographicI
  using ( wfInd-LT₂ )
open import LTC-PCF.Data.Nat.Inequalities using ( GT ; LE ; LT₂ )
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI
  using ( 0>x→⊥
        ; S≤0→⊥
        ; x>y∨x≤y
        ; [Sx∸Sy,Sy]<[Sx,Sy]
        ; [Sx,Sy∸Sx]<[Sx,Sy]
        )
open import LTC-PCF.Data.Nat.PropertiesI using ( ∸-N )

open import LTC-PCF.Program.GCD.Definitions using ( ¬x≡0∧y≡0 )
open import LTC-PCF.Program.GCD.GCD using ( gcd )
open import LTC-PCF.Program.GCD.EquationsI
  using ( gcd-0S ; gcd-S0 ; gcd-S>S ; gcd-S≤S )

------------------------------------------------------------------------------
-- The 'gcd 0 (succ n)' is N.
gcd-0S-N : ∀ {n} → N n → N (gcd zero (succ n))
gcd-0S-N {n} Nn = subst N (sym $ gcd-0S n) (sN Nn)

------------------------------------------------------------------------------
-- The 'gcd (succ n) 0' is N.
gcd-S0-N : ∀ {n} → N n → N (gcd (succ n) zero)
gcd-S0-N {n} Nn = subst N (sym $ gcd-S0 n) (sN Nn)

------------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m > succ n' is N.
gcd-S>S-N : ∀ {m n} → N m → N n →
            N (gcd (succ m ∸ succ n) (succ n)) →
            GT (succ m) (succ n) →
            N (gcd (succ m) (succ n))
gcd-S>S-N {m} {n} Nm Nn ih Sm>Sn = subst N (sym $ gcd-S>S m n Sm>Sn) ih

------------------------------------------------------------------------------

-- The 'gcd (succ m) (succ n)' when 'succ m ≤ succ n' is N.
gcd-S≤S-N : ∀ {m n} → N m → N n →
            N (gcd (succ m) (succ n ∸ succ m)) →
            LE (succ m) (succ n) →
            N (gcd (succ m) (succ n))
gcd-S≤S-N {m} {n} Nm Nn ih Sm≤Sn = subst N (sym $ gcd-S≤S Nm Nn Sm≤Sn) ih

------------------------------------------------------------------------------
-- The 'gcd m n' when 'm > n' is N.
-- N.B. If '>' were an inductive data type, we would use the absurd pattern
-- to prove the second case.
gcd-x>y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → ¬x≡0∧y≡0 o p → N (gcd o p)) →
  GT m n →
  ¬x≡0∧y≡0 m n →
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
-- The 'gcd m n' when 'm ≤ n' is N.
-- N.B. If '≤' were an inductive data type, we would use the absurd pattern
-- to prove the third case.
gcd-x≤y-N :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → ¬x≡0∧y≡0 o p → N (gcd o p)) →
  LE m n →
  ¬x≡0∧y≡0 m n →
  N (gcd m n)
gcd-x≤y-N zN zN _ _  ¬0≡0∧0≡0 = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x≤y-N zN (sN Nn) _ _ _      = gcd-0S-N Nn
gcd-x≤y-N (sN Nm) zN _ Sm≤0  _  = ⊥-elim $ S≤0→⊥ Nm Sm≤0
gcd-x≤y-N (sN {m} Nm) (sN {n} Nn) accH Sm≤Sn _ =
  gcd-S≤S-N Nm Nn ih Sm≤Sn
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
-- The 'gcd' is N.
gcd-N : ∀ {m n} → N m → N n → ¬x≡0∧y≡0 m n → N (gcd m n)
gcd-N = wfInd-LT₂ P istep
  where
    P : D → D → Set
    P i j = ¬x≡0∧y≡0 i j → N (gcd i j)

    istep : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → LT₂ k l i j → P k l) →
            P i j
    istep Ni Nj accH =
      [ gcd-x>y-N Ni Nj accH
      , gcd-x≤y-N Ni Nj accH
      ] (x>y∨x≤y Ni Nj)
