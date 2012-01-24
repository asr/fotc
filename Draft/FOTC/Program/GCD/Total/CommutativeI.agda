------------------------------------------------------------------------------
-- The gcd is commutative
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.FOTC.Program.GCD.Total.CommutativeI where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationProperties
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Program.GCD.Total.EquationsI
open import FOTC.Program.GCD.Total.GCD
open import FOTC.Relation.Binary.EqReasoning

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
Comm d₁ d₂ = gcd d₁ d₂ ≡ gcd d₂ d₁
{-# ATP definition Comm #-}

x>y→y≯x : ∀ {m n} → N m → N n → GT m n → NGT n m
x>y→y≯x zN          Nn          0>n   = ⊥-elim $ 0>x→⊥ Nn 0>n
x>y→y≯x Nm          zN          _     = 0≯x Nm
x>y→y≯x (sN {m} Nm) (sN {n} Nn) Sm>Sn =
  trans (<-SS m n) (x>y→y≯x Nm Nn (trans (sym $ <-SS n m) Sm>Sn))

postulate
  x≯Sy→Sy>x : ∀ {m n} → N m → N n → NGT m (succ₁ n) → GT (succ₁ n) m
-- x≯Sy→Sy>x {n = n} zN      Nn _ = <-0S n
-- x≯Sy→Sy>x {n = n} (sN {m} Nm) Nn h = {!!}

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
               GT (succ₁ m) (succ₁ n) →
               Comm (succ₁ m) (succ₁ n)
gcd-S>S-comm {m} {n} Nm Nn ih Sm>Sn =
  begin
    gcd (succ₁ m) (succ₁ n)
      ≡⟨ gcd-S>S m n Sm>Sn ⟩
    gcd (succ₁ m ∸ succ₁ n) (succ₁ n)
      ≡⟨ ih ⟩
    gcd (succ₁ n) (succ₁ m ∸ succ₁ n)
      ≡⟨ sym (gcd-S≯S n m (x>y→y≯x (sN Nm) (sN Nn) Sm>Sn)) ⟩
    gcd (succ₁ n) (succ₁ m)
  ∎

------------------------------------------------------------------------------
-- gcd (succ₁ m) (succ₁ n) when succ₁ m ≯ succ₁ n is commutative.
gcd-S≯S-comm : ∀ {m n} → N m → N n →
               Comm (succ₁ m) (succ₁ n ∸ succ₁ m) →
               NGT (succ₁ m) (succ₁ n) →
               Comm (succ₁ m) (succ₁ n)
gcd-S≯S-comm {m} {n} Nm Nn ih Sm≯Sn =
  begin
    gcd (succ₁ m) (succ₁ n)
      ≡⟨ gcd-S≯S m n Sm≯Sn ⟩
    gcd (succ₁ m) (succ₁ n ∸ succ₁ m)
      ≡⟨ ih ⟩
    gcd (succ₁ n ∸ succ₁ m) (succ₁ m)
      ≡⟨ sym (gcd-S>S n m (x≯Sy→Sy>x (sN Nm) Nn Sm≯Sn)) ⟩
    gcd (succ₁ n) (succ₁ m)
  ∎

------------------------------------------------------------------------------
-- gcd m n when m > n is commutative.
gcd-x>y-comm :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → Comm o p) →
  GT m n →
  Comm m n
gcd-x>y-comm zN          Nn          _    0>n   = ⊥-elim $ 0>x→⊥ Nn 0>n
gcd-x>y-comm (sN {n} _)  zN          _    _     = gcd-S0-comm n
gcd-x>y-comm (sN {m} Nm) (sN {n} Nn) accH Sm>Sn = gcd-S>S-comm Nm Nn ih Sm>Sn
  where
  -- Inductive hypothesis.
  ih : Comm (succ₁ m ∸ succ₁ n) (succ₁ n)
  ih = accH {succ₁ m ∸ succ₁ n}
            {succ₁ n}
            (∸-N (sN Nm) (sN Nn))
            (sN Nn)
            ([Sx∸Sy,Sy]<[Sx,Sy] Nm Nn)

------------------------------------------------------------------------------
-- gcd m n when m ≯ n is commutative.
gcd-x≯y-comm :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → Comm o p) →
  NGT m n →
  Comm m n
gcd-x≯y-comm zN          zN          _    _     = gcd-00-comm
gcd-x≯y-comm zN          (sN {n} _)  _    _     = sym (gcd-S0-comm n)
gcd-x≯y-comm (sN _)      zN          _    Sm≯0  = ⊥-elim $ S≯0→⊥ Sm≯0
gcd-x≯y-comm (sN {m} Nm) (sN {n} Nn) accH Sm≯Sn = gcd-S≯S-comm Nm Nn ih Sm≯Sn
  where
  -- Inductive hypothesis.
  ih : Comm (succ₁ m) (succ₁ n ∸ succ₁ m)
  ih = accH {succ₁ m}
            {succ₁ n ∸ succ₁ m}
            (sN Nm)
            (∸-N (sN Nn) (sN Nm))
            ([Sx,Sy∸Sx]<[Sx,Sy] Nm Nn)

------------------------------------------------------------------------------
-- gcd is commutative.
gcd-comm : ∀ {m n} → N m → N n → Comm m n
gcd-comm = wfInd-LT₂ P istep
  where
  P : D → D → Set
  P i j = Comm i j

  istep : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → LT₂ k l i j → P k l) →
          P i j
  istep Ni Nj accH =
    [ gcd-x>y-comm Ni Nj accH
    , gcd-x≯y-comm Ni Nj accH
    ] (x>y∨x≯y Ni Nj)
