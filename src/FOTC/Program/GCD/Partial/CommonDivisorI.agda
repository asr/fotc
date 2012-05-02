------------------------------------------------------------------------------
-- The gcd is a common divisor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.GCD.Partial.CommonDivisorI where

open import Common.Function

open import FOTC.Base
open import FOTC.Base.Properties
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility.NotBy0
open import FOTC.Data.Nat.Divisibility.NotBy0.Properties
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesI
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationProperties
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Program.GCD.Partial.Definitions
open import FOTC.Program.GCD.Partial.EquationsI
open import FOTC.Program.GCD.Partial.GCD
open import FOTC.Program.GCD.Partial.TotalityI

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
-- Therefore, instead of prove
--
-- gcd-CD : ... → CD m n (gcd m n)
--
-- using these proofs (i.e. the conjunction of them), we proved it
-- using well-founded induction.

-- gcd 0 (succ n) ∣ 0.
gcd-0S-∣₁ : ∀ {n} → N n → gcd zero (succ₁ n) ∣ zero
gcd-0S-∣₁ {n} Nn = subst (λ x → x ∣ zero)
                         (sym $ gcd-0S n)
                         (S∣0 n)

-- gcd (succ₁ m) 0 ∣ succ₁ m.
gcd-S0-∣₁ : ∀ {m} → N m → gcd (succ₁ m) zero ∣ succ₁ m
gcd-S0-∣₁ {m} Nm = subst (λ x → x ∣ succ₁ m)
                         (sym $ gcd-S0 m)
                         (∣-refl-S Nm)

-- gcd (succ₁ m) (succ₁ n) ∣ succ₁ m, when succ₁ m ≯ succ₁ n.
gcd-S≯S-∣₁ :
  ∀ {m n} → N m → N n →
  (gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ succ₁ m) →
  NGT (succ₁ m) (succ₁ n) →
  gcd (succ₁ m) (succ₁ n) ∣ succ₁ m
gcd-S≯S-∣₁ {m} {n} Nm Nn ih Sm≯Sn =
  subst (λ x → x ∣ succ₁ m)
        (sym $ gcd-S≯S m n Sm≯Sn)
        ih

-- gcd (succ₁ m) (succ₁ n) ∣ succ₁ m when succ₁ m > succ₁ n.
-- We use gcd-∣₂.
-- We apply the theorem that if m∣n and m∣o then m∣(n+o).
gcd-S>S-∣₁ :
  ∀ {m n} → N m → N n →
  (gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ (succ₁ m ∸ succ₁ n)) →
  (gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ succ₁ n) →
  GT (succ₁ m) (succ₁ n) →
  gcd (succ₁ m) (succ₁ n) ∣ succ₁ m

{- Proof:
1. gcd (Sm ∸ Sn) Sn | (Sm ∸ Sn)        IH
2. gcd (Sm ∸ Sn) Sn | Sn               gcd-∣₂
3. gcd (Sm ∸ Sn) Sn | (Sm ∸ Sn) + Sn   m∣n→m∣o→m∣n+o 1,2
4. Sm > Sn                             Hip
5. gcd (Sm ∸ Sn) Sn | Sm               arith-gcd-m>n₂ 3,4
6. gcd Sm Sn = gcd (Sm ∸ Sn) Sn        gcd eq. 4
7. gcd Sm Sn | Sm                      subst 5,6
-}

gcd-S>S-∣₁ {m} {n} Nm Nn ih gcd-∣₂ Sm>Sn =
  -- The first substitution is based on
  --
  -- gcd (succ₁ m) (succ₁ n) = gcd (succ₁ m ∸ succ₁ n) (succ₁ n).
  subst (λ x → x ∣ succ₁ m)
        (sym $ gcd-S>S m n Sm>Sn)
        -- The second substitution is based on m = (m ∸ n) + n.
        (subst (λ y → gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ y)
               (x>y→x∸y+y≡x (sN Nm) (sN Nn) Sm>Sn)
               (x∣y→x∣z→x∣y+z
                 {gcd (succ₁ m ∸ succ₁ n) (succ₁ n)}
                 {succ₁ m ∸ succ₁ n}
                 {succ₁ n}
                 (gcd-N Sm-Sn-N (sN Nn) (λ p → ⊥-elim $ S≢0 $ ∧-proj₂ p))
                 Sm-Sn-N
                 (sN Nn)
                 ih
                 gcd-∣₂
               )
       )
  where
  Sm-Sn-N : N (succ₁ m ∸ succ₁ n)
  Sm-Sn-N = ∸-N (sN Nm) (sN Nn)

------------------------------------------------------------------------------
-- Some case of the gcd-∣₂
-- We don't prove that gcd-∣₂ : ... → gcd m n ∣ n. The reason is
-- the same to don't prove gcd-∣₁ : ... → gcd m n ∣ m.

-- gcd 0 (succ₁ n) ∣₂ succ₁ n.
gcd-0S-∣₂ : ∀ {n} → N n → gcd zero (succ₁ n) ∣ succ₁ n
gcd-0S-∣₂ {n} Nn = subst (λ x → x ∣ succ₁ n)
                         (sym $ gcd-0S n)
                         (∣-refl-S Nn)

-- gcd (succ₁ m) 0 ∣ 0.
gcd-S0-∣₂ : ∀ {m} → N m → gcd (succ₁ m) zero ∣ zero
gcd-S0-∣₂  {m} Nm = subst (λ x → x ∣ zero)
                          (sym $ gcd-S0 m)
                          (S∣0 m)

-- gcd (succ₁ m) (succ₁ n) ∣ succ₁ n when succ₁ m > succ₁ n.
gcd-S>S-∣₂ :
  ∀ {m n} → N m → N n →
  (gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∣ succ₁ n) →
  GT (succ₁ m) (succ₁ n) →
  gcd (succ₁ m) (succ₁ n) ∣ succ₁ n

gcd-S>S-∣₂ {m} {n} Nm Nn ih Sm>Sn =
  subst (λ x → x ∣ succ₁ n)
        (sym $ gcd-S>S m n Sm>Sn)
        ih

-- gcd (succ₁ m) (succ₁ n) ∣ succ₁ n when succ₁ m ≯ succ₁ n.
-- We use gcd-∣₁.
-- We apply the theorem that if m∣n and m∣o then m∣(n+o).
gcd-S≯S-∣₂ :
  ∀ {m n} → N m → N n →
  (gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ (succ₁ n ∸ succ₁ m)) →
  (gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ succ₁ m) →
  NGT (succ₁ m) (succ₁ n) →
  gcd (succ₁ m) (succ₁ n) ∣ succ₁ n

{- Proof:
1. gcd Sm (Sn ∸ Sm) | (Sn ∸ Sm)        IH
2  gcd Sm (Sn ∸ Sm) | Sm               gcd-∣₁
3. gcd Sm (Sn ∸ Sm) | (Sn ∸ Sm) + Sm   m∣n→m∣o→m∣n+o 1,2
4. Sm ≯ Sn                             Hip
5. gcd (Sm ∸ Sn) Sn | Sm               arith-gcd-m≤n₂ 3,4
6. gcd Sm Sn = gcd Sm (Sn ∸ Sm)        gcd eq. 4
7. gcd Sm Sn | Sn                      subst 5,6
-}

gcd-S≯S-∣₂ {m} {n} Nm Nn ih gcd-∣₁ Sm≯Sn =
  -- The first substitution is based on gcd m n = gcd m (n ∸ m).
  subst (λ x → x ∣ succ₁ n)
        (sym $ gcd-S≯S m n Sm≯Sn)
         -- The second substitution is based on n = (n ∸ m) + m.
        (subst (λ y → gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∣ y)
               (x≤y→y∸x+x≡y (sN Nm) (sN Nn) (x≯y→x≤y (sN Nm) (sN Nn) Sm≯Sn))
               (x∣y→x∣z→x∣y+z
                 {gcd (succ₁ m) (succ₁ n ∸ succ₁ m)}
                 {succ₁ n ∸ succ₁ m}
                 {succ₁ m}
                 (gcd-N (sN Nm) Sn-Sm-N (λ p → ⊥-elim $ S≢0 $ ∧-proj₁ p))
                 Sn-Sm-N
                 (sN Nm)
                 ih
                 gcd-∣₁
               )
        )

  where
  Sn-Sm-N : N (succ₁ n ∸ succ₁ m)
  Sn-Sm-N = ∸-N (sN Nn) (sN Nm)

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
  GT (succ₁ m) (succ₁ n) →
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
  NGT (succ₁ m) (succ₁ n) →
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
  (∀ {o p} → N o → N p → LT₂ o p m n → x≢0≢y o p → CD o p (gcd o p)) →
  GT m n →
  x≢0≢y m n →
  CD m n (gcd m n)
gcd-x>y-CD zN Nn _ 0>n _ = ⊥-elim $ 0>x→⊥ Nn 0>n
gcd-x>y-CD (sN Nm) zN _ _ _ = gcd-S0-CD Nm
gcd-x>y-CD (sN {m} Nm) (sN {n} Nn) accH Sm>Sn _ =
  gcd-S>S-CD Nm Nn ih Sm>Sn
  where
  -- Inductive hypothesis.
  ih : CD (succ₁ m ∸ succ₁ n) (succ₁ n) (gcd (succ₁ m ∸ succ₁ n) (succ₁ n))
  ih  = accH {succ₁ m ∸ succ₁ n}
             {succ₁ n}
             (∸-N (sN Nm) (sN Nn))
             (sN Nn)
             ([Sx∸Sy,Sy]<[Sx,Sy] Nm Nn)
             (λ p → ⊥-elim $ S≢0 $ ∧-proj₂ p)

-- The gcd m n when m ≯ n is CD.
gcd-x≯y-CD :
  ∀ {m n} → N m → N n →
  (∀ {o p} → N o → N p → LT₂ o p m n → x≢0≢y o p → CD o p (gcd o p)) →
  NGT m n →
  x≢0≢y m n →
  CD m n (gcd m n)
gcd-x≯y-CD zN          zN          _    _     h = ⊥-elim $ h (refl , refl)
gcd-x≯y-CD zN          (sN Nn)     _    _     _ = gcd-0S-CD Nn
gcd-x≯y-CD (sN _)      zN          _    Sm≯0  _ = ⊥-elim $ S≯0→⊥ Sm≯0
gcd-x≯y-CD (sN {m} Nm) (sN {n} Nn) accH Sm≯Sn _ = gcd-S≯S-CD Nm Nn ih Sm≯Sn
  where
  -- Inductive hypothesis.
  ih : CD (succ₁ m) (succ₁ n ∸ succ₁ m)  (gcd (succ₁ m) (succ₁ n ∸ succ₁ m))
  ih = accH {succ₁ m}
            {succ₁ n ∸ succ₁ m}
            (sN Nm)
            (∸-N (sN Nn) (sN Nm))
            ([Sx,Sy∸Sx]<[Sx,Sy] Nm Nn)
            (λ p → ⊥-elim $ S≢0 $ ∧-proj₁ p)

-- The gcd is CD.
gcd-CD : ∀ {m n} → N m → N n → x≢0≢y m n → CD m n (gcd m n)
gcd-CD = wfInd-LT₂ A istep
  where
  A : D → D → Set
  A i j = x≢0≢y i j → CD i j (gcd i j)

  istep : ∀ {i j} → N i → N j → (∀ {k l} → N k → N l → LT₂ k l i j → A k l) →
          A i j
  istep Ni Nj accH =
    [ gcd-x>y-CD Ni Nj accH
    , gcd-x≯y-CD Ni Nj accH
    ] (x>y∨x≯y Ni Nj)
