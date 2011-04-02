------------------------------------------------------------------------------
-- The gcd is N
------------------------------------------------------------------------------

module FOTC.Program.GCD.IsN-ATP where

open import FOTC.Base
open import FOTC.Base.Properties using ( ¬S≡0 )

open import Common.Function using ( _$_ )

open import FOTC.Data.Nat
  using ( _∸_
        ; N ; sN ; zN  -- The FOTC natural numbers type.
        )
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicATP using ( wfInd-LT₂ )
open import FOTC.Data.Nat.Inequalities using ( GT ; LE ; LT₂)
open import FOTC.Data.Nat.Inequalities.PropertiesATP
  using ( 0>x→⊥
        ; S≤0→⊥
        ; [Sx∸Sy,Sy]<[Sx,Sy]
        ; [Sx,Sy∸Sx]<[Sx,Sy]
        ; x>y∨x≤y
        )
open import FOTC.Data.Nat.PropertiesATP using ( ∸-N )

open import FOTC.Program.GCD.Definitions using ( ¬x≡0∧y≡0 )
open import FOTC.Program.GCD.GCD using ( gcd )

------------------------------------------------------------------------------
-- The 'gcd 0 (succ n)' is N.
postulate
  gcd-0S-N : ∀ {n} → N n → N (gcd zero (succ n))
{-# ATP prove gcd-0S-N #-}

------------------------------------------------------------------------------
-- The 'gcd (succ n) 0' is N.
postulate
  gcd-S0-N : ∀ {n} → N n → N (gcd (succ n) zero)
{-# ATP prove gcd-S0-N #-}

------------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m > succ n' is N.
postulate
  gcd-S>S-N : ∀ {m n} → N m → N n →
              N (gcd (succ m ∸ succ n) (succ n)) →
              GT (succ m) (succ n) →
              N (gcd (succ m) (succ n))
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove gcd-S>S-N #-}

------------------------------------------------------------------------------
-- The 'gcd (succ m) (succ n)' when 'succ m ≤ succ n' is N.
postulate
  gcd-S≤S-N : ∀ {m n} → N m → N n →
              N (gcd (succ m) (succ n ∸ succ m)) →
              LE (succ m) (succ n) →
              N (gcd (succ m) (succ n))
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove gcd-S≤S-N #-}

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
gcd-x≤y-N zN zN _ _  ¬0≡0∧0≡0   = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
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
