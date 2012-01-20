------------------------------------------------------------------------------
-- The gcd is divisible by any common divisor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Program.GCD.Partial.IsDivisibleATP where

open import Common.Function

open import LTC-PCF.Base
open import LTC-PCF.Base.Properties
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Divisibility.NotBy0
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesATP
open import LTC-PCF.Data.Nat.Induction.NonAcc.LexicographicATP
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.EliminationProperties
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP
open import LTC-PCF.Data.Nat.PropertiesATP
open import LTC-PCF.Program.GCD.Partial.Definitions
open import LTC-PCF.Program.GCD.Partial.GCD
open import LTC-PCF.Program.GCD.Partial.EquationsATP

------------------------------------------------------------------------------
-- The gcd 0 (succ n) is Divisible.
postulate
  gcd-0S-Divisible : ∀ {n} → N n → Divisible zero (succ₁ n) (gcd zero (succ₁ n))
{-# ATP prove gcd-0S-Divisible gcd-0S #-}

postulate
  gcd-S0-Divisible : ∀ {n} → N n → Divisible (succ₁ n) zero (gcd (succ₁ n) zero)
{-# ATP prove gcd-S0-Divisible gcd-S0 #-}

------------------------------------------------------------------------------
-- The gcd (succ₁ m) (succ₁ n) when succ₁ m > succ₁ n is Divisible.
-- For the proof using the ATP we added the helper hypothesis
-- c | succ₁ m → c | succ₁ c → c | succ₁ m ∸ succ₁ n.
postulate
  gcd-S>S-Divisible-ah :
    ∀ {m n} → N m → N n →
    (Divisible (succ₁ m ∸ succ₁ n) (succ₁ n) (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))) →
    GT (succ₁ m) (succ₁ n) →
    ∀ c → N c → CD (succ₁ m) (succ₁ n) c →
    (c ∣ succ₁ m ∸ succ₁ n) →
    c ∣ gcd (succ₁ m) (succ₁ n)
-- E 1.2: CPU time limit exceeded (180 sec).
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove gcd-S>S-Divisible-ah gcd-S>S #-}

gcd-S>S-Divisible :
  ∀ {m n} → N m → N n →
  (Divisible (succ₁ m ∸ succ₁ n) (succ₁ n) (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))) →
  GT (succ₁ m) (succ₁ n) →
  Divisible (succ₁ m) (succ₁ n) (gcd (succ₁ m) (succ₁ n))
gcd-S>S-Divisible {m} {n} Nm Nn acc Sm>Sn c Nc (c∣Sm , c∣Sn) =
    gcd-S>S-Divisible-ah Nm Nn acc Sm>Sn c Nc (c∣Sm , c∣Sn)
                         (x∣y→x∣z→x∣y∸z Nc (sN Nm) (sN Nn) c∣Sm c∣Sn)

------------------------------------------------------------------------------
-- The gcd (succ₁ m) (succ₁ n) when succ₁ m ≯ succ₁ n is Divisible.
-- For the proof using the ATP we added the helper hypothesis
-- c | succ₁ n → c | succ₁ m → c | succ₁ n ∸ succ₁ m.
postulate
  gcd-S≯S-Divisible-ah :
    ∀ {m n} → N m → N n →
    (Divisible (succ₁ m) (succ₁ n ∸ succ₁ m) (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))) →
    NGT (succ₁ m) (succ₁ n) →
    ∀ c → N c → CD (succ₁ m) (succ₁ n) c →
    (c ∣ succ₁ n ∸ succ₁ m) →
    c ∣ gcd (succ₁ m) (succ₁ n)
{-# ATP prove gcd-S≯S-Divisible-ah gcd-S≯S #-}

gcd-S≯S-Divisible :
  ∀ {m n} → N m → N n →
  (Divisible (succ₁ m) (succ₁ n ∸ succ₁ m) (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))) →
  NGT (succ₁ m) (succ₁ n) →
  Divisible (succ₁ m) (succ₁ n) (gcd (succ₁ m) (succ₁ n))
gcd-S≯S-Divisible {m} {n} Nm Nn acc Sm≯Sn c Nc (c∣Sm , c∣Sn) =
    gcd-S≯S-Divisible-ah Nm Nn acc Sm≯Sn c Nc (c∣Sm , c∣Sn)
                         (x∣y→x∣z→x∣y∸z Nc (sN Nn) (sN Nm) c∣Sn c∣Sm)

------------------------------------------------------------------------------
-- The gcd m n when m > n is Divisible.
gcd-x>y-Divisible :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → x≠0≠y o p →
             Divisible o p (gcd o p)) →
  GT m n →
  x≠0≠y m n →
  Divisible m n (gcd m n)
gcd-x>y-Divisible zN Nn _ 0>n _ _ _ = ⊥-elim $ 0>x→⊥ Nn 0>n
gcd-x>y-Divisible (sN Nm) zN _ _ _ c Nc = gcd-S0-Divisible Nm c Nc
gcd-x>y-Divisible (sN {m} Nm) (sN {n} Nn) accH Sm>Sn _ c Nc =
  gcd-S>S-Divisible Nm Nn ih Sm>Sn c Nc
  where
  -- Inductive hypothesis.
  ih : Divisible (succ₁ m ∸ succ₁ n) (succ₁ n) (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))
  ih = accH {succ₁ m ∸ succ₁ n}
            {succ₁ n}
            (∸-N (sN Nm) (sN Nn))
            (sN Nn)
            ([Sx∸Sy,Sy]<[Sx,Sy] Nm Nn)
            (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₂ p)

------------------------------------------------------------------------------
-- The gcd m n when m ≯ n is Divisible.
gcd-x≯y-Divisible :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → x≠0≠y o p →
             Divisible o p (gcd o p)) →
  NGT m n →
  x≠0≠y m n →
  Divisible m n (gcd m n)
gcd-x≯y-Divisible zN zN _ _ ¬0≡0∧0≡0 _ _ = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x≯y-Divisible zN (sN Nn) _ _ _  c Nc = gcd-0S-Divisible Nn c Nc
gcd-x≯y-Divisible (sN {m} Nm) zN _ Sm≯0 _ _ _ =
  ⊥-elim (true≠false (trans (sym (<-0S m)) Sm≯0))
gcd-x≯y-Divisible (sN {m} Nm) (sN {n} Nn) accH Sm≯Sn _ c Nc =
  gcd-S≯S-Divisible Nm Nn ih Sm≯Sn c Nc
  where
  -- Inductive hypothesis.
  ih : Divisible (succ₁ m) (succ₁ n ∸ succ₁ m) (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))
  ih = accH {succ₁ m}
            {succ₁ n ∸ succ₁ m}
            (sN Nm)
            (∸-N (sN Nn) (sN Nm))
            ([Sx,Sy∸Sx]<[Sx,Sy] Nm Nn)
            (λ p → ⊥-elim $ ¬S≡0 $ ∧-proj₁ p)

------------------------------------------------------------------------------
-- The gcd is Divisible.
gcd-Divisible : ∀ {m n} → N m → N n → x≠0≠y m n → Divisible m n (gcd m n)
gcd-Divisible = wfInd-LT₂ P istep
  where
  P : D → D → Set
  P i j = x≠0≠y i j → Divisible i j (gcd i j)

  istep : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → LT₂ k l i j → P k l) →
          P i j
  istep Ni Nj accH =
    [ gcd-x>y-Divisible Ni Nj accH
    , gcd-x≯y-Divisible Ni Nj accH
    ] (x>y∨x≯y Ni Nj)
