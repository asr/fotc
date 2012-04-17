------------------------------------------------------------------------------
-- Properties of the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.Inequalities.PropertiesATP where

open import Common.Function

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.EliminationProperties
open import LTC-PCF.Data.Nat.Inequalities.EquationsATP public
open import LTC-PCF.Data.Nat.PropertiesATP

------------------------------------------------------------------------------
-- N.B. The elimination properties are in the module
-- LTC.Data.Nat.Inequalities.EliminationProperties.

x≥0 : ∀ {n} → N n → GE n zero
x≥0 zN          = <-0S zero
x≥0 (sN {n} Nn) = <-0S $ succ₁ n

0≤x : ∀ {n} → N n → LE zero n
0≤x Nn = x≥0 Nn

0≯x : ∀ {n} → N n → NGT zero n
0≯x zN          = <-00
0≯x (sN {n} Nn) = <-S0 n

x≰x : ∀ {n} → N n → NLT n n
x≰x zN          = <-00
x≰x (sN {n} Nn) = trans (<-SS n n) (x≰x Nn)

x<Sx : ∀ {n} → N n → LT n (succ₁ n)
x<Sx zN          = <-0S zero
x<Sx (sN {n} Nn) = trans (<-SS n (succ₁ n)) (x<Sx Nn)

postulate
  x<y→Sx<Sy : ∀ {m n} → LT m n → LT (succ₁ m) (succ₁ n)
{-# ATP prove x<y→Sx<Sy #-}

postulate
  Sx<Sy→x<y : ∀ {m n} → LT (succ₁ m) (succ₁ n) → LT m n
{-# ATP prove Sx<Sy→x<y #-}

x≤x : ∀ {n} → N n → LE n n
x≤x zN          = <-0S zero
x≤x (sN {n} Nn) = trans (<-SS n (succ₁ n)) (x≤x Nn)

x≥x : ∀ {n} → N n → GE n n
x≥x Nn = x≤x Nn

x≤y→Sx≤Sy : ∀ {m n} → LE m n → LE (succ₁ m) (succ₁ n)
x≤y→Sx≤Sy {m} {n} m≤n = trans (<-SS m (succ₁ n)) m≤n

postulate
  Sx≤Sy→x≤y : ∀ {m n} → LE (succ₁ m) (succ₁ n) → LE m n
{-# ATP prove Sx≤Sy→x≤y <-SS #-}

x≥y→x≮y : ∀ {m n} → N m → N n → GE m n → NLT m n
x≥y→x≮y zN          zN          _     = x≰x zN
x≥y→x≮y zN          (sN Nn)     0≥Sn  = ⊥-elim $ 0≥S→⊥ Nn 0≥Sn
x≥y→x≮y (sN {m} Nm) zN          _     = <-S0 m
x≥y→x≮y (sN {m} Nm) (sN {n} Nn) Sm≥Sn =
  prf (x≥y→x≮y Nm Nn (trans (sym $ <-SS n (succ₁ m)) Sm≥Sn))
  where
  postulate prf : NLT m n →  -- IH.
                  NLT (succ₁ m) (succ₁ n)
  {-# ATP prove prf #-}

x≮y→x≥y : ∀ {m n} → N m → N n → NLT m n → GE m n
x≮y→x≥y zN zN 0≮0  = x≥x zN
x≮y→x≥y zN (sN {n} Nn) 0≮Sn = ⊥-elim (true≢false (trans (sym (<-0S n)) 0≮Sn))
x≮y→x≥y (sN Nm) zN Sm≮n = x≥0 (sN Nm)
x≮y→x≥y (sN {m} Nm) (sN {n} Nn) Sm≮Sn =
  prf (x≮y→x≥y Nm Nn (trans (sym (<-SS m n)) Sm≮Sn))
  where
  postulate prf : GE m n →  -- IH.
                  GE (succ₁ m) (succ₁ n)
  {-# ATP prove prf #-}

x>y∨x≤y : ∀ {m n} → N m → N n → GT m n ∨ LE m n
x>y∨x≤y zN          Nn          = inj₂ $ x≥0 Nn
x>y∨x≤y (sN {m} Nm) zN          = inj₁ $ <-0S m
x>y∨x≤y (sN {m} Nm) (sN {n} Nn) =
  [ (λ m>n → inj₁ (trans (<-SS n m) m>n))
  , (λ m≤n → inj₂ (trans (<-SS m (succ₁ n)) m≤n))
  ] (x>y∨x≤y Nm Nn)

x≤y→x≯y : ∀ {m n} → N m → N n → LE m n → NGT m n
x≤y→x≯y zN          Nn          0≤n   = 0≯x Nn
x≤y→x≯y (sN Nm)     zN          Sm≤0  = ⊥-elim (S≤0→⊥ Nm Sm≤0)
x≤y→x≯y (sN {m} Nm) (sN {n} Nn) Sm≤Sn =
  prf (x≤y→x≯y Nm Nn (trans (sym (<-SS m (succ₁ n))) Sm≤Sn))
  where
  postulate prf : NGT m n →  -- IH.
                  NGT (succ₁ m) (succ₁ n)
  {-# ATP prove prf #-}

x≯y→x≤y : ∀ {m n} → N m → N n → NGT m n → LE m n
x≯y→x≤y zN Nn _ = 0≤x Nn
x≯y→x≤y (sN {m} Nm) zN Sm≯0  = ⊥-elim (true≢false (trans (sym (<-0S m)) Sm≯0))
x≯y→x≤y (sN {m} Nm) (sN {n} Nn) Sm≯Sn =
  prf (x≯y→x≤y Nm Nn (trans (sym (<-SS n m)) Sm≯Sn))
  where
  postulate prf : LE m n →  -- IH.
                  LE (succ₁ m) (succ₁ n)
  {-# ATP prove prf #-}

x>y∨x≯y : ∀ {m n} → N m → N n → GT m n ∨ NGT m n
x>y∨x≯y Nm Nn = [ (λ m>n → inj₁ m>n) ,
                  (λ m≤n → inj₂ (x≤y→x≯y Nm Nn m≤n))
                ] (x>y∨x≤y Nm Nn)

x<y∨x≥y : ∀ {m n} → N m → N n → LT m n ∨ GE m n
x<y∨x≥y Nm Nn = x>y∨x≤y Nn Nm

x<y∨x≮y : ∀ {m n} → N m → N n → LT m n ∨ NLT m n
x<y∨x≮y Nm Nn = [ (λ m<n → inj₁ m<n)
                , (λ m≥n → inj₂ (x≥y→x≮y Nm Nn m≥n))
                ] (x<y∨x≥y Nm Nn)

x≡y→x≤y : ∀ {m n} → N m → N n → m ≡ n → LE m n
x≡y→x≤y {n = n} Nm Nn m≡n = subst (λ m' → LE m' n) (sym m≡n) (x≤x Nn)

x<y→x≤y : ∀ {m n} → N m → N n → LT m n → LE m n
x<y→x≤y Nm zN          m<0            = ⊥-elim $ x<0→⊥ Nm m<0
x<y→x≤y zN (sN {n} Nn)          _     = <-0S $ succ₁ n
x<y→x≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn =
  x≤y→Sx≤Sy (x<y→x≤y Nm Nn (Sx<Sy→x<y Sm<Sn))

x<Sy→x≤y : ∀ {m n} → N m → N n → LT m (succ₁ n) → LE m n
x<Sy→x≤y zN Nn 0<Sn       = 0≤x Nn
x<Sy→x≤y (sN Nm) Nn Sm<Sn = Sm<Sn

x≤Sx : ∀ {m} → N m → LE m (succ₁ m)
x≤Sx Nm = x<y→x≤y Nm (sN Nm) (x<Sx Nm)

x<y→Sx≤y : ∀ {m n} → N m → N n → LT m n → LE (succ₁ m) n
x<y→Sx≤y Nm          zN          m<0   = ⊥-elim $ x<0→⊥ Nm m<0
x<y→Sx≤y zN          (sN {n} Nn) 0<Sn  = x≤y→Sx≤Sy (0≤x Nn)
x<y→Sx≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn = trans (<-SS (succ₁ m) (succ₁ n)) Sm<Sn

Sx≤y→x<y : ∀ {m n} → N m → N n → LE (succ₁ m) n → LT m n
Sx≤y→x<y Nm          zN          Sm≤0   = ⊥-elim $ S≤0→⊥ Nm Sm≤0
Sx≤y→x<y zN          (sN {n} Nn) _      = <-0S n
Sx≤y→x<y (sN {m} Nm) (sN {n} Nn) SSm≤Sn =
  x<y→Sx<Sy (Sx≤y→x<y Nm Nn (Sx≤Sy→x≤y SSm≤Sn))

<-trans : ∀ {m n o} → N m → N n → N o → LT m n → LT n o → LT m o
<-trans zN          zN           _          0<0   _    = ⊥-elim $ 0<0→⊥ 0<0
<-trans zN          (sN Nn)     zN          _     Sn<0 = ⊥-elim $ S<0→⊥ Sn<0
<-trans zN          (sN Nn)     (sN {o} No) _     _    = <-0S o
<-trans (sN Nm)     Nn          zN          _     n<0  = ⊥-elim $ x<0→⊥ Nn n<0
<-trans (sN Nm)     zN          (sN No)     Sm<0  _    = ⊥-elim $ S<0→⊥ Sm<0
<-trans (sN {m} Nm) (sN {n} Nn) (sN {o} No) Sm<Sn Sn<So =
  x<y→Sx<Sy $ <-trans Nm Nn No (Sx<Sy→x<y Sm<Sn) (Sx<Sy→x<y Sn<So)

≤-trans : ∀ {m n o} → N m → N n → N o → LE m n → LE n o → LE m o
≤-trans zN      Nn              No          _     _     = 0≤x No
≤-trans (sN Nm) zN              No          Sm≤0  _     = ⊥-elim $ S≤0→⊥ Nm Sm≤0
≤-trans (sN Nm) (sN Nn)         zN          _     Sn≤0  = ⊥-elim $ S≤0→⊥ Nn Sn≤0
≤-trans (sN {m} Nm) (sN {n} Nn) (sN {o} No) Sm≤Sn Sn≤So =
  x≤y→Sx≤Sy (≤-trans Nm Nn No (Sx≤Sy→x≤y Sm≤Sn) (Sx≤Sy→x≤y Sn≤So))

x≤x+y : ∀ {m n} → N m → N n → LE m (m + n)
x≤x+y         zN          Nn = x≥0 (+-N zN Nn)
x≤x+y {n = n} (sN {m} Nm) Nn = prf $ x≤x+y Nm Nn
  where
  postulate prf : LE m (m + n) →  -- IH.
                  LE (succ₁ m) (succ₁ m + n)
  {-# ATP prove prf +-Sx <-SS #-}

x∸y<Sx : ∀ {m n} → N m → N n → LT (m ∸ n) (succ₁ m)
x∸y<Sx {m} Nm zN = prf
  where
  postulate prf : LT (m ∸ zero) (succ₁ m)
  {-# ATP prove prf x<Sx ∸-x0 #-}

x∸y<Sx zN (sN {n} Nn) = prf
  where
  postulate prf : LT (zero ∸ succ₁ n) (succ₁ zero)
  {-# ATP prove prf ∸-0S ∸-0S <-0S #-}

x∸y<Sx (sN {m} Nm) (sN {n} Nn) = prf $ x∸y<Sx Nm Nn
  where
  postulate prf : LT (m ∸ n) (succ₁ m) →  -- IH.
                  LT (succ₁ m ∸ succ₁ n) (succ₁ (succ₁ m))
  {-# ATP prove prf <-trans ∸-N x<Sx ∸-SS #-}

postulate Sx∸Sy<Sx : ∀ {m n} → N m → N n → LT (succ₁ m ∸ succ₁ n) (succ₁ m)
{-# ATP prove Sx∸Sy<Sx ∸-SS x∸y<Sx #-}

x>y→x∸y+y≡x : ∀ {m n} → N m → N n → GT m n → (m ∸ n) + n ≡ m
x>y→x∸y+y≡x zN Nn 0>n = ⊥-elim $ 0>x→⊥ Nn 0>n
x>y→x∸y+y≡x (sN {m} Nm) zN Sm>0 = prf
  where
  postulate prf : (succ₁ m ∸ zero) + zero ≡ succ₁ m
  {-# ATP prove prf +-rightIdentity ∸-N ∸-x0 #-}

x>y→x∸y+y≡x (sN {m} Nm) (sN {n} Nn) Sm>Sn = prf $ x>y→x∸y+y≡x Nm Nn m>n
  where
  postulate m>n : GT m n
  {-# ATP prove m>n <-SS #-}

  postulate prf : (m ∸ n) + n ≡ m →  -- IH.
                  (succ₁ m ∸ succ₁ n) + succ₁ n ≡ succ₁ m
  {-# ATP prove prf +-comm ∸-N +-Sx ∸-SS <-SS #-}

x≤y→y∸x+x≡y : ∀ {m n} → N m → N n → LE m n → (n ∸ m) + m ≡ n
x≤y→y∸x+x≡y {n = n} zN Nn 0≤n  = prf
  where
  postulate prf : (n ∸ zero) + zero ≡ n
  {-# ATP prove prf +-rightIdentity ∸-N ∸-x0 <-SS #-}

x≤y→y∸x+x≡y (sN Nm) zN Sm≤0 = ⊥-elim $ S≤0→⊥ Nm Sm≤0

x≤y→y∸x+x≡y (sN {m} Nm) (sN {n} Nn) Sm≤Sn = prf $ x≤y→y∸x+x≡y Nm Nn m≤n
  where
  postulate m≤n : LE m n
  {-# ATP prove m≤n <-SS #-}

  postulate prf : (n ∸ m) + m ≡ n →  -- IH.
                  (succ₁ n ∸ succ₁ m) + succ₁ m ≡ succ₁ n
  {-# ATP prove prf +-comm ∸-N +-Sx ∸-SS <-SS #-}

x<y→x<Sy : ∀ {m n} → N m → N n → LT m n → LT m (succ₁ n)
x<y→x<Sy Nm          zN          m<0   = ⊥-elim $ x<0→⊥ Nm m<0
x<y→x<Sy zN          (sN {n} Nn) 0<Sn  = <-0S $ succ₁ n
x<y→x<Sy (sN {m} Nm) (sN {n} Nn) Sm<Sn =
  x<y→Sx<Sy (x<y→x<Sy Nm Nn (Sx<Sy→x<y Sm<Sn))

x<Sy→x<y∨x≡y : ∀ {m n} → N m → N n → LT m (succ₁ n) → LT m n ∨ m ≡ n
x<Sy→x<y∨x≡y zN zN 0<S0 = inj₂ refl
x<Sy→x<y∨x≡y zN (sN {n} Nn) 0<SSn = inj₁ (<-0S n)
x<Sy→x<y∨x≡y (sN {m} Nm) zN Sm<S0 =
  ⊥-elim $ x<0→⊥ Nm (trans (sym $ <-SS m zero) Sm<S0)
x<Sy→x<y∨x≡y (sN {m} Nm) (sN {n} Nn) Sm<SSn =
  [ (λ m<n → inj₁ (trans (<-SS m n) m<n))
  , (λ m≡n → inj₂ (cong succ₁ m≡n))
  ]
  m<n∨m≡n

  where
  m<n∨m≡n : LT m n ∨ m ≡ n
  m<n∨m≡n = x<Sy→x<y∨x≡y Nm Nn (trans (sym $ <-SS m (succ₁ n)) Sm<SSn)

x≤y→x<y∨x≡y : ∀ {m n} → N m → N n → LE m n → LT m n ∨ m ≡ n
x≤y→x<y∨x≡y = x<Sy→x<y∨x≡y

postulate x<y→y≡z→x<z : ∀ {m n o} → LT m n → n ≡ o → LT m o
{-# ATP prove x<y→y≡z→x<z #-}

postulate x≡y→y<z→x<z : ∀ {m n o} → m ≡ n → LT n o → LT m o
{-# ATP prove x≡y→y<z→x<z #-}

x≥y→y>0→x∸y<x : ∀ {m n} → N m → N n → GE m n → GT n zero → LT (m ∸ n) m
x≥y→y>0→x∸y<x Nm          zN          _     0>0  = ⊥-elim $ x>x→⊥ zN 0>0
x≥y→y>0→x∸y<x zN          (sN Nn)     0≥Sn  _    = ⊥-elim $ S≤0→⊥ Nn 0≥Sn
x≥y→y>0→x∸y<x (sN {m} Nm) (sN {n} Nn) Sm≥Sn Sn>0 = prf
  where
  postulate prf : LT (succ₁ m ∸ succ₁ n) (succ₁ m)
  {-# ATP prove prf ∸-SS x∸y<Sx #-}

------------------------------------------------------------------------------
-- Properties about LT₂

-- TODO: 2012-04-17. Is it possible to eliminate the FOTC types?
postulate xy<00→⊥ : ∀ {m n} → N m → N n → ¬ (LT₂ m n zero zero)
{-# ATP prove xy<00→⊥ x<0→⊥ #-}

-- TODO: 2012-04-17. Is it possible to eliminate the FOTC types?
postulate 0Sx<00→⊥ : ∀ {m} → ¬ (LT₂ zero (succ₁ m) zero zero)
{-# ATP prove 0Sx<00→⊥ S<0→⊥ #-}

postulate Sxy₁<0y₂→⊥ : ∀ {m n₁ n₂} → ¬ (LT₂ (succ₁ m) n₁ zero n₂)
{-# ATP prove Sxy₁<0y₂→⊥ #-}

-- TODO: 2012-04-17. Is it possible to eliminate the FOTC types?
postulate x₁y<x₂0→x₁<x₂ : ∀ {m₁ n} → N n → ∀ {m₂} → LT₂ m₁ n m₂ zero → LT m₁ m₂
{-# ATP prove x₁y<x₂0→x₁<x₂ x<0→⊥ #-}

-- TODO: 2012-04-17. Is it possible to eliminate the FOTC types?
postulate
  xy₁<0y₂→x≡0∧y₁<y₂ : ∀ {m} → N m → ∀ {n₁ n₂} → LT₂ m n₁ zero n₂ →
                      m ≡ zero ∧ LT n₁ n₂
{-# ATP prove xy₁<0y₂→x≡0∧y₁<y₂ x<0→⊥ #-}

[Sx∸Sy,Sy]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     LT₂ (succ₁ m ∸ succ₁ n) (succ₁ n) (succ₁ m) (succ₁ n)
[Sx∸Sy,Sy]<[Sx,Sy] {m} {n} Nm Nn = prf
  where
  postulate prf : LT₂ (succ₁ m ∸ succ₁ n) (succ₁ n) (succ₁ m) (succ₁ n)
  {-# ATP prove prf Sx∸Sy<Sx #-}

[Sx,Sy∸Sx]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     LT₂ (succ₁ m) (succ₁ n ∸ succ₁ m) (succ₁ m) (succ₁ n)
[Sx,Sy∸Sx]<[Sx,Sy] {m} {n} Nm Nn = prf
  where
  postulate prf : LT₂ (succ₁ m) (succ₁ n ∸ succ₁ m) (succ₁ m) (succ₁ n)
  {-# ATP prove prf sN Sx∸Sy<Sx #-}
