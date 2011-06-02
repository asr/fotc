------------------------------------------------------------------------------
-- The gcd is divisible by any common divisor (using equational reasoning)
------------------------------------------------------------------------------

module FOTC.Program.GCD.IsDivisibleI where

open import FOTC.Base
open import FOTC.Base.Properties

open import Common.Function

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility
open import FOTC.Data.Nat.Divisibility.PropertiesI
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI

open import FOTC.Program.GCD.Definitions
open import FOTC.Program.GCD.EquationsI
open import FOTC.Program.GCD.GCD

------------------------------------------------------------------------------
-- The gcd 0 (succ n) is Divisible.
gcd-0S-Divisible : ∀ {n} → N n → Divisible zero (succ n) (gcd zero (succ n))
gcd-0S-Divisible {n} _ c _ (c∣0 , c∣Sn) =
  subst (λ x → c ∣ x) (sym $ gcd-0S n) c∣Sn

------------------------------------------------------------------------------
-- The gcd (succ n) 0 is Divisible.
gcd-S0-Divisible : ∀ {n} → N n → Divisible (succ n) zero (gcd (succ n) zero)
gcd-S0-Divisible {n} _ c _ (c∣Sn , c∣0) =
  subst (λ x → c ∣ x) (sym $ gcd-S0 n) c∣Sn

------------------------------------------------------------------------------
-- The gcd (succ m) (succ n) when succ m > succ n is Divisible.
gcd-S>S-Divisible :
  ∀ {m n} → N m → N n →
  (Divisible (succ m ∸ succ n) (succ n) (gcd (succ m ∸ succ n) (succ n))) →
  GT (succ m) (succ n) →
  Divisible (succ m) (succ n) (gcd (succ m) (succ n))
gcd-S>S-Divisible {m} {n} Nm Nn acc Sm>Sn c Nc (c∣Sm , c∣Sn) =
{-
Proof:
   ----------------- (Hip.)
     c | m    c | n
   ---------------------- (Thm.)   -------- (Hip.)
       c | (m ∸ n)                   c | n
     ------------------------------------------ (IH)
              c | gcd m (n ∸ m)                          m > n
             --------------------------------------------------- (gcd def.)
                             c | gcd m n
-}
 subst (λ x → c ∣ x)
       (sym $ gcd-S>S m n Sm>Sn)
       (acc c Nc (c|Sm-Sn , c∣Sn))
 where
 c|Sm-Sn : c ∣ succ m ∸ succ n
 c|Sm-Sn = x∣y→x∣z→x∣y∸z Nc (sN Nm) (sN Nn) c∣Sm c∣Sn

------------------------------------------------------------------------------
-- The gcd (succ m) (succ n) when succ m ≯ succ n is Divisible.
gcd-S≯S-Divisible :
  ∀ {m n} → N m → N n →
  (Divisible (succ m) (succ n ∸ succ m) (gcd (succ m) (succ n ∸ succ m))) →
  NGT (succ m) (succ n) →
  Divisible (succ m) (succ n) (gcd (succ m) (succ n))
gcd-S≯S-Divisible {m} {n} Nm Nn acc Sm≯Sn c Nc (c∣Sm , c∣Sn) =
{-
Proof
                            ----------------- (Hip.)
                                c | m    c | n
        -------- (Hip.)       ---------------------- (Thm.)
         c | m                      c | n ∸ m
     ------------------------------------------ (IH)
              c | gcd m (n ∸ m)                          m ≯ n
             --------------------------------------------------- (gcd def.)
                             c | gcd m n
-}

  subst (λ x → c ∣ x)
        (sym $ gcd-S≯S m n Sm≯Sn)
        (acc c Nc (c∣Sm , c|Sn-Sm))
  where
  c|Sn-Sm : c ∣ succ n ∸ succ m
  c|Sn-Sm = x∣y→x∣z→x∣y∸z Nc (sN Nn) (sN Nm) c∣Sn c∣Sm

------------------------------------------------------------------------------
-- The gcd m n when m > n is Divisible.
gcd-x>y-Divisible :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → x≠0≠y o p →
             Divisible o p (gcd o p)) →
  GT m n →
  x≠0≠y m n →
  Divisible m n (gcd m n)
gcd-x>y-Divisible zN zN _ _ ¬0≡0∧0≡0 _ _  = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x>y-Divisible zN (sN Nn) _ 0>Sn _ _ _ = ⊥-elim $ 0>x→⊥ (sN Nn) 0>Sn
gcd-x>y-Divisible (sN Nm) zN _ _ _  c Nc  = gcd-S0-Divisible Nm c Nc
gcd-x>y-Divisible (sN {m} Nm) (sN {n} Nn) accH Sm>Sn _ c Nc =
  gcd-S>S-Divisible Nm Nn ih Sm>Sn c Nc
  where
  -- Inductive hypothesis.
  ih : Divisible (succ m ∸ succ n) (succ n) (gcd (succ m ∸ succ n) (succ n))
  ih = accH {succ m ∸ succ n}
            {succ n}
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
gcd-x≯y-Divisible zN zN _ _ ¬0≡0∧0≡0 _ _   = ⊥-elim $ ¬0≡0∧0≡0 (refl , refl)
gcd-x≯y-Divisible zN (sN Nn) _ _  _  c Nc  = gcd-0S-Divisible Nn c Nc
gcd-x≯y-Divisible (sN {m} Nm) zN _ Sm≯0 _ _ _  =
  ⊥-elim (true≠false (trans (sym (<-0S m)) Sm≯0))
gcd-x≯y-Divisible (sN {m} Nm) (sN {n} Nn) accH Sm≯Sn _ c Nc =
  gcd-S≯S-Divisible Nm Nn ih Sm≯Sn c Nc
  where
  -- Inductive hypothesis.
  ih : Divisible (succ m) (succ n ∸ succ m) (gcd (succ m) (succ n ∸ succ m))
  ih = accH {succ m}
            {succ n ∸ succ m}
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
