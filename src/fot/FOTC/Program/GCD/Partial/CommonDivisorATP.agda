------------------------------------------------------------------------------
-- The gcd is a common divisor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.GCD.Partial.CommonDivisorATP where

open import FOTC.Base
open import FOTC.Base.PropertiesATP
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility.NotBy0
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesATP
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicATP
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationProperties
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Program.GCD.Partial.Definitions
open import FOTC.Program.GCD.Partial.GCD
open import FOTC.Program.GCD.Partial.TotalityATP

------------------------------------------------------------------------------
-- Some cases of the gcd-∣₁.

-- We don't prove that
--
-- gcd-∣₁ : ... → (gcd m n) ∣ m

-- because this proof should be defined mutually recursive with the
-- proof
--
-- gcd-∣₂ : ... → (gcd m n) ∣ n.
--
-- Therefore, instead of proving
--
-- gcd-CD : ... → CD m n (gcd m n)
--
-- using these proofs (i.e. the conjunction of them), we proved it
-- using well-founded induction.

-- gcd 0 (succ n) ∣ 0.
postulate gcd-0S-∣₁ : ∀ {n} → N n → gcd zero (succ₁ n) ∣ zero
{-# ATP prove gcd-0S-∣₁ #-}

-- gcd (succ₁ m) 0 ∣ succ₁ m.
postulate gcd-S0-∣₁ : ∀ {n} → N n → gcd (succ₁ n) zero ∣ succ₁ n
{-# ATP prove gcd-S0-∣₁ ∣-refl-S #-}

-- gcd (succ₁ m) (succ₁ n) ∣ succ₁ m, when succ₁ m ≯ succ₁ n.
postulate
  gcd-S≯S-∣₁ :
    ∀ {m n} → N m → N n →
    (gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ succ₁ m) →
    succ₁ m ≯ succ₁ n →
    gcd (succ₁ m) (succ₁ n) ∣ succ₁ m
{-# ATP prove gcd-S≯S-∣₁ #-}

-- gcd (succ₁ m) (succ₁ n) ∣ succ₁ m when succ₁ m > succ₁ n.
{- Proof:
1. gcd (Sm ∸ Sn) Sn | (Sm ∸ Sn)        IH
2. gcd (Sm ∸ Sn) Sn | Sn               gcd-∣₂
3. gcd (Sm ∸ Sn) Sn | (Sm ∸ Sn) + Sn   m∣n→m∣o→m∣n+o 1,2
4. Sm > Sn                             Hip
5. gcd (Sm ∸ Sn) Sn | Sm               arith-gcd-m>n₂ 3,4
6. gcd Sm Sn = gcd (Sm ∸ Sn) Sn        gcd eq. 4
7. gcd Sm Sn | Sm                      subst 5,6
-}

-- For the proof using the ATP we added the helper hypothesis:
-- 1. gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ (succ₁ m ∸ succ₁ n) + succ₁ n.
-- 2. (succ₁ m ∸ succ₁ n) + succ₁ n ≡ succ₁ m.
postulate
  gcd-S>S-∣₁-ah :
    ∀ {m n} → N m → N n →
    (gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ (succ₁ m ∸ succ₁ n)) →
    (gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ succ₁ n) →
    succ₁ m > succ₁ n →
    gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ (succ₁ m ∸ succ₁ n) + succ₁ n →
    ((succ₁ m ∸ succ₁ n) + succ₁ n ≡ succ₁ m) →
    gcd (succ₁ m) (succ₁ n) ∣ succ₁ m
{-# ATP prove gcd-S>S-∣₁-ah #-}

gcd-S>S-∣₁ :
  ∀ {m n} → N m → N n →
  (gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ (succ₁ m ∸ succ₁ n)) →
  (gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ succ₁ n) →
  succ₁ m > succ₁ n →
  gcd (succ₁ m) (succ₁ n) ∣ succ₁ m
gcd-S>S-∣₁ {m} {n} Nm Nn ih gcd-∣₂ Sm>Sn =
  gcd-S>S-∣₁-ah Nm Nn ih gcd-∣₂ Sm>Sn
    (x∣y→x∣z→x∣y+z gcd-Sm-Sn,Sn-N Sm-Sn-N (nsucc Nn) ih gcd-∣₂)
    (x>y→x∸y+y≡x (nsucc Nm) (nsucc Nn) Sm>Sn)

  where
  Sm-Sn-N : N (succ₁ m ∸ succ₁ n)
  Sm-Sn-N = ∸-N (nsucc Nm) (nsucc Nn)

  gcd-Sm-Sn,Sn-N : N (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))
  gcd-Sm-Sn,Sn-N = gcd-N Sm-Sn-N (nsucc Nn) (λ p → ⊥-elim (S≢0 (∧-proj₂ p)))

------------------------------------------------------------------------------
-- Some case of the gcd-∣₂.
-- We don't prove that gcd-∣₂ : ... → gcd m n ∣ n. The reason is
-- the same to don't prove gcd-∣₁ : ... → gcd m n ∣ m.

-- gcd 0 (succ₁ n) ∣₂ succ₁ n.
postulate gcd-0S-∣₂ : ∀ {n} → N n → gcd zero (succ₁ n) ∣ succ₁ n
{-# ATP prove gcd-0S-∣₂ ∣-refl-S #-}

-- gcd (succ₁ m) 0 ∣ 0.
postulate gcd-S0-∣₂ : ∀ {m} → N m → gcd (succ₁ m) zero ∣ zero
{-# ATP prove gcd-S0-∣₂ #-}

-- gcd (succ₁ m) (succ₁ n) ∣ succ₁ n when succ₁ m ≯ succ₁ n.
{- Proof:
1. gcd Sm (Sn ∸ Sm) | (Sn ∸ Sm)        IH
2  gcd Sm (Sn ∸ Sm) | Sm               gcd-∣₁
3. gcd Sm (Sn ∸ Sm) | (Sn ∸ Sm) + Sm   m∣n→m∣o→m∣n+o 1,2
4. Sm ≯ Sn                             Hip
5. gcd (Sm ∸ Sn) Sn | Sm               arith-gcd-m≤n₂ 3,4
6. gcd Sm Sn = gcd Sm (Sn ∸ Sm)        gcd eq. 4
7. gcd Sm Sn | Sn                      subst 5,6
-}

-- For the proof using the ATP we added the helper hypothesis:
-- 1. gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ (succ₁ n ∸ succ₁ m) + succ₁ m.
-- 2 (succ₁ n ∸ succ₁ m) + succ₁ m ≡ succ₁ n.
postulate
  gcd-S≯S-∣₂-ah :
    ∀ {m n} → N m → N n →
    (gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ (succ₁ n ∸ succ₁ m)) →
    (gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ succ₁ m) →
    succ₁ m ≯ succ₁ n →
    (gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ (succ₁ n ∸ succ₁ m) + succ₁ m) →
    ((succ₁ n ∸ succ₁ m) + succ₁ m ≡ succ₁ n) →
    gcd (succ₁ m) (succ₁ n) ∣ succ₁ n
{-# ATP prove gcd-S≯S-∣₂-ah #-}

gcd-S≯S-∣₂ :
  ∀ {m n} → N m → N n →
  (gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ (succ₁ n ∸ succ₁ m)) →
  (gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ succ₁ m) →
  succ₁ m ≯ succ₁ n →
  gcd (succ₁ m) (succ₁ n) ∣ succ₁ n
gcd-S≯S-∣₂ {m} {n} Nm Nn ih gcd-∣₁ Sm≯Sn =
  gcd-S≯S-∣₂-ah Nm Nn ih gcd-∣₁ Sm≯Sn
    (x∣y→x∣z→x∣y+z gcd-Sm,Sn-Sm-N Sn-Sm-N (nsucc Nm) ih gcd-∣₁)
    (x≤y→y∸x+x≡y (nsucc Nm) (nsucc Nn) (x≯y→x≤y (nsucc Nm) (nsucc Nn) Sm≯Sn))

  where
  Sn-Sm-N : N (succ₁ n ∸ succ₁ m)
  Sn-Sm-N = ∸-N (nsucc Nn) (nsucc Nm)

  gcd-Sm,Sn-Sm-N : N (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))
  gcd-Sm,Sn-Sm-N = gcd-N (nsucc Nm) (Sn-Sm-N) (λ p → ⊥-elim (S≢0 (∧-proj₁ p)))

-- gcd (succ₁ m) (succ₁ n) ∣ succ₁ n when succ₁ m > succ₁ n.
postulate
  gcd-S>S-∣₂ :
    ∀ {m n} → N m → N n →
    (gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ succ₁ n) →
    succ₁ m > succ₁ n →
    gcd (succ₁ m) (succ₁ n) ∣ succ₁ n
{-# ATP prove gcd-S>S-∣₂ #-}

------------------------------------------------------------------------------
-- The gcd is CD.
-- We will prove that gcd-CD : ... → CD m n (gcd m n).

-- The gcd 0 (succ₁ n) is CD.
gcd-0S-CD : ∀ {n} → N n → CD zero (succ₁ n) (gcd zero (succ₁ n))
gcd-0S-CD Nn = (gcd-0S-∣₁ Nn , gcd-0S-∣₂ Nn)

-- The gcd (succ₁ m) 0 is CD.
gcd-S0-CD : ∀ {m} → N m → CD (succ₁ m) zero (gcd (succ₁ m) zero)
gcd-S0-CD Nm = (gcd-S0-∣₁ Nm , gcd-S0-∣₂ Nm)

-- The gcd (succ₁ m) (succ₁ n) when succ₁ m > succ₁ n is CD.
gcd-S>S-CD :
  ∀ {m n} → N m → N n →
  (CD (succ₁ m ∸ succ₁ n) (succ₁ n) (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))) →
  succ₁ m > succ₁ n →
  CD (succ₁ m) (succ₁ n) (gcd (succ₁ m) (succ₁ n))
gcd-S>S-CD {m} {n} Nm Nn acc Sm>Sn =
   (gcd-S>S-∣₁ Nm Nn acc-∣₁ acc-∣₂ Sm>Sn , gcd-S>S-∣₂ Nm Nn acc-∣₂ Sm>Sn)
  where
  acc-∣₁ : gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ (succ₁ m ∸ succ₁ n)
  acc-∣₁ = ∧-proj₁ acc

  acc-∣₂ : gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ succ₁ n
  acc-∣₂ = ∧-proj₂ acc

-- The gcd (succ₁ m) (succ₁ n) when succ₁ m ≯ succ₁ n is CD.
gcd-S≯S-CD :
  ∀ {m n} → N m → N n →
  (CD (succ₁ m) (succ₁ n ∸ succ₁ m) (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))) →
  succ₁ m ≯ succ₁ n →
  CD (succ₁ m) (succ₁ n) (gcd (succ₁ m) (succ₁ n))
gcd-S≯S-CD {m} {n} Nm Nn acc Sm≯Sn =
  (gcd-S≯S-∣₁ Nm Nn acc-∣₁ Sm≯Sn , gcd-S≯S-∣₂ Nm Nn acc-∣₂ acc-∣₁ Sm≯Sn)
  where
  acc-∣₁ : gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ succ₁ m
  acc-∣₁ = ∧-proj₁ acc

  acc-∣₂ : gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ (succ₁ n ∸ succ₁ m)
  acc-∣₂ = ∧-proj₂ acc

-- The gcd m n when m > n is CD.
gcd-x>y-CD :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → Lexi o p m n → x≢0≢y o p → CD o p (gcd o p)) →
  m > n →
  x≢0≢y m n →
  CD m n (gcd m n)
gcd-x>y-CD nzero          Nn             _  0>n   _ = ⊥-elim (0>x→⊥ Nn 0>n)
gcd-x>y-CD (nsucc Nm)     nzero          _  _     _ = gcd-S0-CD Nm
gcd-x>y-CD (nsucc {m} Nm) (nsucc {n} Nn) ah Sm>Sn _ =
  gcd-S>S-CD Nm Nn ih Sm>Sn
  where
  -- Inductive hypothesis.
  ih : CD (succ₁ m ∸ succ₁ n) (succ₁ n) (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))
  ih  = ah {succ₁ m ∸ succ₁ n}
           {succ₁ n}
           (∸-N (nsucc Nm) (nsucc Nn))
           (nsucc Nn)
           ([Sx∸Sy,Sy]<[Sx,Sy] Nm Nn)
           (λ p → ⊥-elim (S≢0 (∧-proj₂ p)))

-- The gcd m n when m ≯ n is CD.
gcd-x≯y-CD :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → Lexi o p m n → x≢0≢y o p → CD o p (gcd o p)) →
  m ≯ n →
  x≢0≢y m n →
  CD m n (gcd m n)
gcd-x≯y-CD nzero          nzero         _   _     h = ⊥-elim (h (refl , refl))
gcd-x≯y-CD nzero          (nsucc Nn)     _  _     _ = gcd-0S-CD Nn
gcd-x≯y-CD (nsucc _)      nzero          _  Sm≯0  _ = ⊥-elim (S≯0→⊥ Sm≯0)
gcd-x≯y-CD (nsucc {m} Nm) (nsucc {n} Nn) ah Sm≯Sn _ = gcd-S≯S-CD Nm Nn ih Sm≯Sn
  where
  -- Inductive hypothesis.
  ih : CD (succ₁ m) (succ₁ n ∸ succ₁ m)  (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))
  ih = ah {succ₁ m}
          {succ₁ n ∸ succ₁ m}
          (nsucc Nm)
          (∸-N (nsucc Nn) (nsucc Nm))
          ([Sx,Sy∸Sx]<[Sx,Sy] Nm Nn)
          (λ p → ⊥-elim (S≢0 (∧-proj₁ p)))

-- The gcd is CD.
gcd-CD : ∀ {m n} → N m → N n → x≢0≢y m n → CD m n (gcd m n)
gcd-CD = Lexi-wfind A h
  where
  A : D → D → Set
  A i j = x≢0≢y i j → CD i j (gcd i j)

  h : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → Lexi k l i j → A k l) →
      A i j
  h Ni Nj ah = case (gcd-x>y-CD Ni Nj ah) (gcd-x≯y-CD Ni Nj ah) (x>y∨x≯y Ni Nj)
