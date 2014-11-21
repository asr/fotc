------------------------------------------------------------------------------
-- The gcd is commutative
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Program.GCD.Total.CommutativeI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationPropertiesI
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Program.GCD.Total.ConversionRulesI
open import FOTC.Program.GCD.Total.GCD

------------------------------------------------------------------------------
-- Informal proof:
-- 1. gcd 0 n = n        -- gcd def
--            = gcd n 0  -- gcd def

-- 2. gcd n 0 = n        -- gcd def
--            = gcd 0 n  -- gcd def

-- 3.1. Case: S m > S n
-- gcd (S m) (S n) = gcd (S m - S n) (S n)  -- gcd def
--                 = gcd (S n) (S m - S n)  -- IH
--                 = gcd (S n) (S m)        -- gcd def

-- 3.2. Case: S m ≮ S n
-- gcd (S m) (S n) = gcd (S m) (S n - S m)  -- gcd def
--                 = gcd (S n - S m) (S m)  -- IH
--                 = gcd (S n) (S m)        -- gcd def

------------------------------------------------------------------------------
-- Commutativity property.
Comm : D → D → Set
Comm t t' = gcd t t' ≡ gcd t' t
{-# ATP definition Comm #-}

x>y→y≯x : ∀ {m n} → N m → N n → m > n → n ≯ m
x>y→y≯x nzero          Nn             0>n   = ⊥-elim (0>x→⊥ Nn 0>n)
x>y→y≯x Nm             nzero          _     = 0≯x Nm
x>y→y≯x (nsucc {m} Nm) (nsucc {n} Nn) Sm>Sn =
  trans (lt-SS m n) (x>y→y≯x Nm Nn (trans (sym (lt-SS n m)) Sm>Sn))

postulate x≯Sy→Sy>x : ∀ {m n} → N m → N n → m ≯ succ₁ n → succ₁ n > m
-- x≯Sy→Sy>x {n = n} nzero      Nn _ = <-0S n
-- x≯Sy→Sy>x {n = n} (nsucc {m} Nm) Nn h = {!!}

------------------------------------------------------------------------------
-- gcd 0 0 is commutative.
gcd-00-comm : Comm zero zero
gcd-00-comm = refl

------------------------------------------------------------------------------
-- gcd (succ₁ n) 0 is commutative.
gcd-S0-comm : ∀ n → Comm (succ₁ n) zero
gcd-S0-comm n = trans (gcd-S0 n) (sym (gcd-0S n))

------------------------------------------------------------------------------
-- gcd (succ₁ m) (succ₁ n) when succ₁ m > succ₁ n is commutative.
gcd-S>S-comm : ∀ {m n} → N m → N n →
               Comm (succ₁ m ∸ succ₁ n) (succ₁ n) →
               succ₁ m > succ₁ n →
               Comm (succ₁ m) (succ₁ n)
gcd-S>S-comm {m} {n} Nm Nn ih Sm>Sn =
  gcd (succ₁ m) (succ₁ n)
    ≡⟨ gcd-S>S m n Sm>Sn ⟩
  gcd (succ₁ m ∸ succ₁ n) (succ₁ n)
    ≡⟨ ih ⟩
  gcd (succ₁ n) (succ₁ m ∸ succ₁ n)
    ≡⟨ sym (gcd-S≯S n m (x>y→y≯x (nsucc Nm) (nsucc Nn) Sm>Sn)) ⟩
  gcd (succ₁ n) (succ₁ m) ∎

------------------------------------------------------------------------------
-- gcd (succ₁ m) (succ₁ n) when succ₁ m ≯ succ₁ n is commutative.
gcd-S≯S-comm : ∀ {m n} → N m → N n →
               Comm (succ₁ m) (succ₁ n ∸ succ₁ m) →
               succ₁ m ≯ succ₁ n →
               Comm (succ₁ m) (succ₁ n)
gcd-S≯S-comm {m} {n} Nm Nn ih Sm≯Sn =
  gcd (succ₁ m) (succ₁ n)
    ≡⟨ gcd-S≯S m n Sm≯Sn ⟩
  gcd (succ₁ m) (succ₁ n ∸ succ₁ m)
    ≡⟨ ih ⟩
  gcd (succ₁ n ∸ succ₁ m) (succ₁ m)
    ≡⟨ sym (gcd-S>S n m (x≯Sy→Sy>x (nsucc Nm) Nn Sm≯Sn)) ⟩
  gcd (succ₁ n) (succ₁ m) ∎

------------------------------------------------------------------------------
-- gcd m n when m > n is commutative.
gcd-x>y-comm :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → Lexi o p m n → Comm o p) →
  m > n →
  Comm m n
gcd-x>y-comm nzero          Nn             _  0>n   = ⊥-elim (0>x→⊥ Nn 0>n)
gcd-x>y-comm (nsucc {n} _)  nzero          _  _     = gcd-S0-comm n
gcd-x>y-comm (nsucc {m} Nm) (nsucc {n} Nn) ah Sm>Sn = gcd-S>S-comm Nm Nn ih Sm>Sn
  where
  -- Inductive hypothesis.
  ih : Comm (succ₁ m ∸ succ₁ n) (succ₁ n)
  ih = ah {succ₁ m ∸ succ₁ n}
          {succ₁ n}
          (∸-N (nsucc Nm) (nsucc Nn))
          (nsucc Nn)
          ([Sx∸Sy,Sy]<[Sx,Sy] Nm Nn)

------------------------------------------------------------------------------
-- gcd m n when m ≯ n is commutative.
gcd-x≯y-comm :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → Lexi o p m n → Comm o p) →
  m ≯ n →
  Comm m n
gcd-x≯y-comm nzero          nzero          _  _     = gcd-00-comm
gcd-x≯y-comm nzero          (nsucc {n} _)  _  _     = sym (gcd-S0-comm n)
gcd-x≯y-comm (nsucc _)      nzero          _  Sm≯0  = ⊥-elim (S≯0→⊥ Sm≯0)
gcd-x≯y-comm (nsucc {m} Nm) (nsucc {n} Nn) ah Sm≯Sn = gcd-S≯S-comm Nm Nn ih Sm≯Sn
  where
  -- Inductive hypothesis.
  ih : Comm (succ₁ m) (succ₁ n ∸ succ₁ m)
  ih = ah {succ₁ m}
          {succ₁ n ∸ succ₁ m}
          (nsucc Nm)
          (∸-N (nsucc Nn) (nsucc Nm))
          ([Sx,Sy∸Sx]<[Sx,Sy] Nm Nn)

------------------------------------------------------------------------------
-- gcd is commutative.
gcd-comm : ∀ {m n} → N m → N n → Comm m n
gcd-comm = Lexi-wfind A h
  where
  A : D → D → Set
  A i j = Comm i j

  h : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → Lexi k l i j → A k l) →
      A i j
  h Ni Nj ah = case (gcd-x>y-comm Ni Nj ah)
                    (gcd-x≯y-comm Ni Nj ah)
                    (x>y∨x≯y Ni Nj)
