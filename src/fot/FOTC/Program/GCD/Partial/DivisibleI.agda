------------------------------------------------------------------------------
-- The gcd is divisible by any common divisor (using equational reasoning)
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.GCD.Partial.DivisibleI where

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility.NotBy0
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesI
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationPropertiesI
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Program.GCD.Partial.ConversionRulesI
open import FOTC.Program.GCD.Partial.Definitions
open import FOTC.Program.GCD.Partial.GCD

------------------------------------------------------------------------------
-- The gcd 0 (succ n) is Divisible.
gcd-0S-Divisible : ∀ {n} → N n → Divisible zero (succ₁ n) (gcd zero (succ₁ n))
gcd-0S-Divisible {n} _ c _ (c∣0 , c∣Sn) = subst (_∣_ c) (sym (gcd-0S n)) c∣Sn

------------------------------------------------------------------------------
-- The gcd (succ₁ n) 0 is Divisible.
gcd-S0-Divisible : ∀ {n} → N n → Divisible (succ₁ n) zero (gcd (succ₁ n) zero)
gcd-S0-Divisible {n} _ c _ (c∣Sn , c∣0) = subst (_∣_ c) (sym (gcd-S0 n)) c∣Sn

------------------------------------------------------------------------------
-- The gcd (succ₁ m) (succ₁ n) when succ₁ m > succ₁ n is Divisible.
gcd-S>S-Divisible :
  ∀ {m n} → N m → N n →
  (Divisible (succ₁ m ∸ succ₁ n) (succ₁ n) (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))) →
  succ₁ m > succ₁ n →
  Divisible (succ₁ m) (succ₁ n) (gcd (succ₁ m) (succ₁ n))
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
 subst (_∣_ c) (sym (gcd-S>S m n Sm>Sn)) (acc c Nc (c|Sm-Sn , c∣Sn))
 where
 c|Sm-Sn : c ∣ succ₁ m ∸ succ₁ n
 c|Sm-Sn = x∣y→x∣z→x∣y∸z Nc (nsucc Nm) (nsucc Nn) c∣Sm c∣Sn

------------------------------------------------------------------------------
-- The gcd (succ₁ m) (succ₁ n) when succ₁ m ≯ succ₁ n is Divisible.
gcd-S≯S-Divisible :
  ∀ {m n} → N m → N n →
  (Divisible (succ₁ m) (succ₁ n ∸ succ₁ m) (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))) →
  succ₁ m ≯ succ₁ n →
  Divisible (succ₁ m) (succ₁ n) (gcd (succ₁ m) (succ₁ n))
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

  subst (_∣_ c) (sym (gcd-S≯S m n Sm≯Sn)) (acc c Nc (c∣Sm , c|Sn-Sm))
  where
  c|Sn-Sm : c ∣ succ₁ n ∸ succ₁ m
  c|Sn-Sm = x∣y→x∣z→x∣y∸z Nc (nsucc Nn) (nsucc Nm) c∣Sn c∣Sm

------------------------------------------------------------------------------
-- The gcd m n when m > n is Divisible.
gcd-x>y-Divisible :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → Lexi o p m n → x≢0≢y o p →
             Divisible o p (gcd o p)) →
  m > n →
  x≢0≢y m n →
  Divisible m n (gcd m n)
gcd-x>y-Divisible nzero nzero _ _ ¬0≡0∧0≡0 _ _  = ⊥-elim (¬0≡0∧0≡0 (refl , refl))
gcd-x>y-Divisible nzero (nsucc Nn) _ 0>Sn _ _ _ = ⊥-elim (0>x→⊥ (nsucc Nn) 0>Sn)
gcd-x>y-Divisible (nsucc Nm) nzero _ _ _  c Nc  = gcd-S0-Divisible Nm c Nc
gcd-x>y-Divisible (nsucc {m} Nm) (nsucc {n} Nn) ah Sm>Sn _ c Nc =
  gcd-S>S-Divisible Nm Nn ih Sm>Sn c Nc
  where
  -- Inductive hypothesis.
  ih : Divisible (succ₁ m ∸ succ₁ n) (succ₁ n) (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))
  ih = ah {succ₁ m ∸ succ₁ n}
          {succ₁ n}
          (∸-N (nsucc Nm) (nsucc Nn))
          (nsucc Nn)
          ([Sx∸Sy,Sy]<[Sx,Sy] Nm Nn)
          (λ p → ⊥-elim (S≢0 (∧-proj₂ p)))

------------------------------------------------------------------------------
-- The gcd m n when m ≯ n is Divisible.
gcd-x≯y-Divisible :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → Lexi o p m n → x≢0≢y o p →
             Divisible o p (gcd o p)) →
  m ≯ n →
  x≢0≢y m n →
  Divisible m n (gcd m n)
gcd-x≯y-Divisible nzero nzero _ _ h _ _   = ⊥-elim (h (refl , refl))
gcd-x≯y-Divisible nzero (nsucc Nn) _ _  _  c Nc  = gcd-0S-Divisible Nn c Nc
gcd-x≯y-Divisible (nsucc _) nzero _ Sm≯0 _ _ _  = ⊥-elim (S≯0→⊥ Sm≯0)
gcd-x≯y-Divisible (nsucc {m} Nm) (nsucc {n} Nn) ah Sm≯Sn _ c Nc =
  gcd-S≯S-Divisible Nm Nn ih Sm≯Sn c Nc
  where
  -- Inductive hypothesis.
  ih : Divisible (succ₁ m) (succ₁ n ∸ succ₁ m) (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))
  ih = ah {succ₁ m}
          {succ₁ n ∸ succ₁ m}
          (nsucc Nm)
          (∸-N (nsucc Nn) (nsucc Nm))
          ([Sx,Sy∸Sx]<[Sx,Sy] Nm Nn)
          (λ p → ⊥-elim (S≢0 (∧-proj₁ p)))

------------------------------------------------------------------------------
-- The gcd is Divisible.
gcdDivisible : ∀ {m n} → N m → N n → x≢0≢y m n → Divisible m n (gcd m n)
gcdDivisible = Lexi-wfind A h
  where
  A : D → D → Set
  A i j = x≢0≢y i j → Divisible i j (gcd i j)

  h : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → Lexi k l i j → A k l) →
      A i j
  h Ni Nj ah = case (gcd-x>y-Divisible Ni Nj ah)
                    (gcd-x≯y-Divisible Ni Nj ah)
                    (x>y∨x≯y Ni Nj)
