------------------------------------------------------------------------------
-- Properties of the inequalities
------------------------------------------------------------------------------

module FOTC.Data.Nat.Inequalities.PropertiesATP where

open import FOTC.Base

open import Common.Function using ( _$_ )

open import FOTC.Data.Nat
  using ( _+_ ; _∸_ ; ∸-SS
        ; N ; sN ; zN  -- The FOTC natural numbers type
        )
open import FOTC.Data.Nat.Inequalities
  using ( <-00 ; <-0S ; <-S0 ; <-SS
        ; GE ; GT ; LE ; LT ; NGT ; NLE ; NLT
        ; LT₂
        )
open import FOTC.Data.Nat.Inequalities.Properties public
open import FOTC.Data.Nat.PropertiesATP
  using ( +-N ; ∸-N
        ; +-comm
        ; +-rightIdentity
        ; ∸-0x
        )

------------------------------------------------------------------------------

x≥0 : ∀ {n} → N n → GE n zero
x≥0 zN          = <-0S zero
x≥0 (sN {n} Nn) = <-0S $ succ n

0≤x : ∀ {n} → N n → LE zero n
0≤x Nn = x≥0 Nn

0≯x : ∀ {n} → N n → NGT zero n
0≯x zN          = <-00
0≯x (sN {n} Nn) = <-S0 n

x≰x : ∀ {n} → N n → NLT n n
x≰x zN          = <-00
x≰x (sN {n} Nn) = trans (<-SS n n) (x≰x Nn)

S≰0 : ∀ {n} → N n → NLE (succ n) zero
S≰0 zN          = x≰x (sN zN)
S≰0 (sN {n} Nn) = trans (<-SS (succ n) zero) (<-S0 n)

x<Sx : ∀ {n} → N n → LT n (succ n)
x<Sx zN          = <-0S zero
x<Sx (sN {n} Nn) = trans (<-SS n (succ n)) (x<Sx Nn)

postulate
  x<y→Sx<Sy : ∀ {m n} → LT m n → LT (succ m) (succ n)
{-# ATP prove x<y→Sx<Sy #-}

postulate
  Sx<Sy→x<y : ∀ {m n} → LT (succ m) (succ n) → LT m n
{-# ATP prove Sx<Sy→x<y #-}

x≤x : ∀ {n} → N n → LE n n
x≤x zN          = <-0S zero
x≤x (sN {n} Nn) = trans (<-SS n (succ n)) (x≤x Nn)

x≥x : ∀ {n} → N n → GE n n
x≥x Nn = x≤x Nn

x≤y→Sx≤Sy : ∀ {m n} → LE m n → LE (succ m) (succ n)
x≤y→Sx≤Sy {m} {n} m≤n = trans (<-SS m (succ n)) m≤n

postulate
  Sx≤Sy→x≤y : ∀ {m n} → LE (succ m) (succ n) → LE m n
{-# ATP prove Sx≤Sy→x≤y #-}

x≰y→Sx≰Sy : ∀ m n → NLE m n → NLE (succ m) (succ n)
x≰y→Sx≰Sy m n m≰n = trans (<-SS m (succ n)) m≰n

x>y→y<x : ∀ {m n} → N m → N n → GT m n → LT n m
x>y→y<x zN          Nn          0>n   = ⊥-elim $ 0>x→⊥ Nn 0>n
x>y→y<x (sN {m} Nm) zN          _     = <-0S m
x>y→y<x (sN {m} Nm) (sN {n} Nn) Sm>Sn =
  trans (<-SS n m) (x>y→y<x Nm Nn (trans (sym $ <-SS n m) Sm>Sn))

x≥y→x≮y : ∀ {m n} → N m → N n → GE m n → NLT m n
x≥y→x≮y zN          zN          _     = x≰x zN
x≥y→x≮y zN          (sN Nn)     0≥Sn  = ⊥-elim $ 0≥S→⊥ Nn 0≥Sn
x≥y→x≮y (sN {m} Nm) zN          _     = <-S0 m
x≥y→x≮y (sN {m} Nm) (sN {n} Nn) Sm≥Sn =
  trans (<-SS m n) (x≥y→x≮y Nm Nn (trans (sym $ <-SS n (succ m)) Sm≥Sn))

x>y→x≰y : ∀ {m n} → N m → N n → GT m n → NLE m n
x>y→x≰y zN          Nn          0>m   = ⊥-elim $ 0>x→⊥ Nn 0>m
x>y→x≰y (sN Nm)     zN          _     = S≰0 Nm
x>y→x≰y (sN {m} Nm) (sN {n} Nn) Sm>Sn =
  x≰y→Sx≰Sy m n (x>y→x≰y Nm Nn (trans (sym $ <-SS n m) Sm>Sn))

postulate
  x>y→x≤y→⊥ : ∀ {m n} → N m → N n → GT m n → LE m n → ⊥
{-# ATP prove x>y→x≤y→⊥ x>y→x≰y #-}

x>y∨x≤y : ∀ {m n} → N m → N n → GT m n ∨ LE m n
x>y∨x≤y zN          Nn          = inj₂ $ x≥0 Nn
x>y∨x≤y (sN {m} Nm) zN          = inj₁ $ <-0S m
x>y∨x≤y (sN {m} Nm) (sN {n} Nn) =
  [ (λ m>n → inj₁ (trans (<-SS n m) m>n))
  , (λ m≤n → inj₂ (x≤y→Sx≤Sy m≤n))
  ] (x>y∨x≤y Nm Nn)

x<y∨x≥y : ∀ {m n} → N m → N n → LT m n ∨ GE m n
x<y∨x≥y Nm Nn = x>y∨x≤y Nn Nm

x≤y∨x≰y : ∀ {m n} → N m → N n → LE m n ∨ NLE m n
x≤y∨x≰y zN Nn = inj₁ (0≤x Nn)
x≤y∨x≰y (sN Nm) zN = inj₂ (S≰0 Nm)
x≤y∨x≰y (sN {m} Nm) (sN {n} Nn) =
  [ (λ m≤n → inj₁ (x≤y→Sx≤Sy m≤n))
  , (λ m≰n → inj₂ (x≰y→Sx≰Sy m n m≰n))
  ] (x≤y∨x≰y Nm Nn)

x≡y→x≤y : ∀ {m n} {Nm : N m} {Nn : N n} → m ≡ n → LE m n
x≡y→x≤y {Nm = Nm} refl = x≤x Nm

x<y→x≤y : ∀ {m n} → N m → N n → LT m n → LE m n
x<y→x≤y Nm zN          m<0            = ⊥-elim $ x<0→⊥ Nm m<0
x<y→x≤y zN (sN {n} Nn)          _     = <-0S $ succ n
x<y→x≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn =
  x≤y→Sx≤Sy (x<y→x≤y Nm Nn (Sx<Sy→x<y Sm<Sn))

x<Sy→x≤y : ∀ {m n} → N m → N n → LT m (succ n) → LE m n
x<Sy→x≤y zN Nn 0<Sn       = 0≤x Nn
x<Sy→x≤y (sN Nm) Nn Sm<Sn = Sm<Sn

x≤y→x<Sy : ∀ {m n} → N m → N n → LE m n → LT m (succ n)
x≤y→x<Sy {n = n} zN      Nn 0≤n  = <-0S n
x≤y→x<Sy         (sN Nm) Nn Sm≤n = Sm≤n

x≤Sx : ∀ {m} → N m → LE m (succ m)
x≤Sx Nm = x<y→x≤y Nm (sN Nm) (x<Sx Nm)

x<y→Sx≤y : ∀ {m n} → N m → N n → LT m n → LE (succ m) n
x<y→Sx≤y Nm          zN          m<0   = ⊥-elim $ x<0→⊥ Nm m<0
x<y→Sx≤y zN          (sN Nn)     0<Sn  = x≤y→Sx≤Sy (0≤x Nn)
x<y→Sx≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn = trans (<-SS (succ m) (succ n)) Sm<Sn

Sx≤y→x<y : ∀ {m n} → N m → N n → LE (succ m) n → LT m n
Sx≤y→x<y Nm          zN          Sm≤0   = ⊥-elim $ S≤0→⊥ Nm Sm≤0
Sx≤y→x<y zN          (sN {n} Nn) _      = <-0S n
Sx≤y→x<y (sN {m} Nm) (sN {n} Nn) SSm≤Sn =
  x<y→Sx<Sy (Sx≤y→x<y Nm Nn (Sx≤Sy→x≤y SSm≤Sn))

x≤y→x≯y : ∀ {m n} → N m → N n → LE m n → NGT m n
x≤y→x≯y zN          Nn          0≤n   = 0≯x Nn
x≤y→x≯y (sN Nm)     zN          Sm≤0  = ⊥-elim (S≤0→⊥ Nm Sm≤0)
x≤y→x≯y (sN {m} Nm) (sN {n} Nn) Sm≤Sn =
  prf (x≤y→x≯y Nm Nn (trans (sym (<-SS m (succ n))) Sm≤Sn))
  where
    postulate prf : NGT m n →  -- IH.
                    NGT (succ m) (succ n)
    {-# ATP prove prf #-}

x≯y→x≤y : ∀ {m n} → N m → N n → NGT m n → LE m n
x≯y→x≤y zN          Nn          _     = 0≤x Nn
x≯y→x≤y (sN {m} Nm) zN          Sm≯0  = ⊥-elim (true≠false
                                                 (trans (sym (<-0S m)) Sm≯0))
x≯y→x≤y (sN {m} Nm) (sN {n} Nn) Sm≯Sn =
  prf (x≯y→x≤y Nm Nn (trans (sym (<-SS n m)) Sm≯Sn))
  where
    postulate prf : LE m n →  -- IH.
                    LE (succ m) (succ n)
    {-# ATP prove prf #-}

x>y∨x≯y : ∀ {m n} → N m → N n → GT m n ∨ NGT m n
x>y∨x≯y Nm Nn = [ (λ m>n → inj₁ m>n) ,
                  (λ m≤n → inj₂ (x≤y→x≯y Nm Nn m≤n))
                ] (x>y∨x≤y Nm Nn)

<-trans : ∀ {m n o} → N m → N n → N o → LT m n → LT n o → LT m o
<-trans zN          zN          _           0<0   _     = ⊥-elim $ 0<0→⊥ 0<0
<-trans zN          (sN Nn)     zN          _     Sn<0  = ⊥-elim $ S<0→⊥ Sn<0
<-trans zN          (sN Nn)     (sN {o} No) _     _     = <-0S o
<-trans (sN Nm)     Nn          zN          _     n<0   = ⊥-elim $ x<0→⊥ Nn n<0
<-trans (sN Nm)     zN          (sN No)     Sm<0  _     = ⊥-elim $ S<0→⊥ Sm<0
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
                    LE (succ m) (succ m + n)
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    {-# ATP prove prf #-}

x<x+Sy : ∀ {m n} → N m → N n → LT m (m + succ n)
x<x+Sy {n = n} zN Nn = prf0
  where
    postulate prf0 : LT zero (zero + succ n)
    {-# ATP prove prf0 #-}
x<x+Sy {n = n} (sN {m} Nm) Nn = prfS (x<x+Sy Nm Nn)
  where
    postulate prfS : LT m (m + succ n) → LT (succ m) (succ m + succ n)
    {-# ATP prove prfS #-}

k+x<k+y→x<y : ∀ {m n k} → N m → N n → N k → LT (k + m) (k + n) → LT m n
k+x<k+y→x<y {m} {n} Nm Nn zN h = prf0
  where
    postulate prf0 : LT m n
    {-# ATP prove prf0 #-}
k+x<k+y→x<y {m} {n} Nm Nn (sN {k} Nk) h = k+x<k+y→x<y Nm Nn Nk prfS
  where
    postulate prfS : LT (k + m) (k + n)
    {-# ATP prove prfS #-}

postulate x+k<y+k→x<y : ∀ {m n k} → N m → N n → N k →
                        LT (m + k) (n + k) → LT m n
{-# ATP prove x+k<y+k→x<y k+x<k+y→x<y +-comm #-}

x≤y→k+x≤k+y : ∀ {m n k} → N m → N n → N k → LE m n → LE (k + m) (k + n)
x≤y→k+x≤k+y {m} {n} Nm Nn zN h = prf0
  where
    postulate prf0 : LE (zero + m) (zero + n)
    {-# ATP prove prf0 #-}
x≤y→k+x≤k+y {m} {n} Nm Nn (sN {k} Nk) h = prfS (x≤y→k+x≤k+y Nm Nn Nk h)
  where
    postulate prfS : LE (k + m) (k + n) → LE (succ k + m) (succ k + n)
    {-# ATP prove prfS #-}

postulate x≤y→x+k≤y+k : ∀ {m n k} → N m → N n → N k → LE m n →
                        LE (m + k) (n + k)
{-# ATP prove x≤y→x+k≤y+k x≤y→k+x≤k+y +-comm #-}

x<y→Sx∸y≡0 : ∀ {m n} → N m → N n → LT m n → succ m ∸ n ≡ zero
x<y→Sx∸y≡0 Nm zN h = ⊥-elim (x<0→⊥ Nm h)
x<y→Sx∸y≡0 zN (sN {n} Nn) h = prf0S
  where
    postulate prf0S : succ zero ∸ succ n ≡ zero
    {-# ATP prove prf0S ∸-0x #-}
x<y→Sx∸y≡0 (sN {m} Nm) (sN {n} Nn) h = prfSS (x<y→Sx∸y≡0 Nm Nn m<n)
  where
    postulate m<n : LT m n
    {-# ATP prove m<n #-}

    postulate prfSS : succ m ∸ n ≡ zero → succ (succ m) ∸ succ n ≡ zero
    {-# ATP prove prfSS #-}

postulate x≤y→x-y≡0 : ∀ {m n} → N m → N n → LE m n → (m ∸ n) ≡ zero
{-# ATP prove x≤y→x-y≡0 x<y→Sx∸y≡0 #-}

x<y→0<y∸x : ∀ {m n} → N m → N n → LT m n → LT zero (n ∸ m)
x<y→0<y∸x Nm zN h = ⊥-elim (x<0→⊥ Nm h)
x<y→0<y∸x zN (sN {n} Nn) h = prf0S
  where
    postulate prf0S : LT zero (succ n ∸ zero)
    {-# ATP prove prf0S #-}

x<y→0<y∸x (sN {m} Nm) (sN {n} Nn) h = prfSS (x<y→0<y∸x Nm Nn m<n)
  where
    postulate m<n : LT m n
    {-# ATP prove m<n #-}

    postulate prfSS : LT zero (n ∸ m) → LT zero (succ n ∸ succ m)
    {-# ATP prove prfSS #-}

0<x∸y→0<Sx∸y : ∀ {m n} → N m → N n → LT zero (m ∸ n) → LT zero (succ m ∸ n)
0<x∸y→0<Sx∸y {m} Nm zN h = prfx0
  where
    postulate prfx0 : LT zero (succ m ∸ zero)
    {-# ATP prove prfx0 #-}

0<x∸y→0<Sx∸y zN (sN {n} Nn) h = ⊥-elim (x<0→⊥ zN h')
  where
    postulate h' : LT zero zero
    {-# ATP prove h' #-}

0<x∸y→0<Sx∸y (sN {m} Nm) (sN {n} Nn) h = prfSS (0<x∸y→0<Sx∸y Nm Nn 0<m-n)
  where
    postulate 0<m-n : LT zero (m ∸ n)
    {-# ATP prove 0<m-n #-}

    postulate prfSS : LT zero (succ m ∸ n) → LT zero (succ (succ m) ∸ succ n)
    {-# ATP prove prfSS <-trans #-}

x∸y<Sx : ∀ {m n} → N m → N n → LT (m ∸ n) (succ m)
x∸y<Sx {m} Nm zN = prf
  where
    postulate prf : LT (m ∸ zero) (succ m)
    {-# ATP prove prf x<Sx #-}

x∸y<Sx zN (sN {n} Nn) = prf
  where
    postulate prf : LT (zero ∸ succ n) (succ zero)
    {-# ATP prove prf #-}

x∸y<Sx (sN {m} Nm) (sN {n} Nn) = prf $ x∸y<Sx Nm Nn
  where
    postulate prf : LT (m ∸ n) (succ m) →  -- IH.
                    LT (succ m ∸ succ n) (succ (succ m))
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    {-# ATP prove prf <-trans ∸-N x<Sx #-}

postulate
  Sx∸Sy<Sx : ∀ {m n} → N m → N n → LT (succ m ∸ succ n) (succ m)
{-# ATP prove Sx∸Sy<Sx x∸y<Sx #-}

x<x∸y→⊥ : ∀ {m n} → N m → N n → ¬ (LT m (m ∸ n))
x<x∸y→⊥ {m} Nm zN m<m∸0 = prf
  where
    postulate prf : ⊥
    {-# ATP prove prf x<x→⊥ #-}
x<x∸y→⊥ zN (sN Nn) 0<0∸Sn = prf
 where
   postulate prf : ⊥
   {-# ATP prove prf x<x→⊥ #-}
x<x∸y→⊥ (sN Nm) (sN Nn) Sm<Sm∸Sn = prf
  where
    postulate prf : ⊥
    {-# ATP prove prf ∸-N x<y→y<x→⊥ x∸y<Sx #-}

x∸Sy≤x∸y : ∀ {m n} → N m → N n → LE (m ∸ succ n) (m ∸ n)
x∸Sy≤x∸y {n = n} zN Nn = prf
  where
    postulate prf : LE (zero ∸ succ n) (zero ∸ n)
    {-# ATP prove prf 0≤x #-}

x∸Sy≤x∸y (sN {m} Nm) zN = prf
  where
    postulate prf : LE (succ m ∸ succ zero) (succ m ∸ zero)
    {-# ATP prove prf x≤Sx #-}

x∸Sy≤x∸y (sN {m} Nm) (sN {n} Nn) = prf (x∸Sy≤x∸y Nm Nn)
  where
    postulate prf : LE (m ∸ succ n) (m ∸ n) →  -- IH.
                    LE (succ m ∸ succ (succ n)) (succ m ∸ (succ n))
    {-# ATP prove prf #-}

x>y→x∸y+y≡x : ∀ {m n} → N m → N n → GT m n → (m ∸ n) + n ≡ m
x>y→x∸y+y≡x zN          Nn 0>n  = ⊥-elim $ 0>x→⊥ Nn 0>n
x>y→x∸y+y≡x (sN {m} Nm) zN Sm>0 = prf
  where
    postulate prf : (succ m ∸ zero) + zero ≡ succ m
    {-# ATP prove prf +-rightIdentity ∸-N #-}

x>y→x∸y+y≡x (sN {m} Nm) (sN {n} Nn) Sm>Sn = prf $ x>y→x∸y+y≡x Nm Nn m>n
  where
    postulate m>n : GT m n
    {-# ATP prove m>n #-}

    postulate prf : (m ∸ n) + n ≡ m →  -- IH.
                    (succ m ∸ succ n) + succ n ≡ succ m
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
    {-# ATP prove prf +-comm ∸-N #-}

x≤y→y∸x+x≡y : ∀ {m n} → N m → N n → LE m n → (n ∸ m) + m ≡ n
x≤y→y∸x+x≡y {n = n} zN Nn 0≤n  = prf
  where
    postulate prf : (n ∸ zero) + zero ≡ n
    {-# ATP prove prf +-rightIdentity ∸-N #-}

x≤y→y∸x+x≡y (sN Nm) zN Sm≤0 = ⊥-elim $ S≤0→⊥ Nm Sm≤0

x≤y→y∸x+x≡y (sN {m} Nm) (sN {n} Nn) Sm≤Sn = prf $ x≤y→y∸x+x≡y Nm Nn m≤n
  where
    postulate m≤n : LE m n
    {-# ATP prove m≤n #-}

    postulate prf : (n ∸ m) + m ≡ n →  -- IH.
                    (succ n ∸ succ m) + succ m ≡ succ n
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
    {-# ATP prove prf +-comm ∸-N #-}

x<y→x<Sy : ∀ {m n} → N m → N n → LT m n → LT m (succ n)
x<y→x<Sy Nm          zN          m<0   = ⊥-elim $ x<0→⊥ Nm m<0
x<y→x<Sy zN          (sN {n} Nn) 0<Sn  = <-0S $ succ n
x<y→x<Sy (sN {m} Nm) (sN {n} Nn) Sm<Sn =
  x<y→Sx<Sy (x<y→x<Sy Nm Nn (Sx<Sy→x<y Sm<Sn))

x<Sy→x<y∨x≡y : ∀ {m n} → N m → N n → LT m (succ n) → LT m n ∨ m ≡ n
x<Sy→x<y∨x≡y zN zN 0<S0 = inj₂ refl
x<Sy→x<y∨x≡y zN (sN {n} Nn) 0<SSn = inj₁ (<-0S n)
x<Sy→x<y∨x≡y (sN {m} Nm) zN Sm<S0 =
  ⊥-elim $ x<0→⊥ Nm (trans (sym $ <-SS m zero) Sm<S0)
x<Sy→x<y∨x≡y (sN {m} Nm) (sN {n} Nn) Sm<SSn =
  [ (λ m<n → inj₁ (trans (<-SS m n) m<n))
  , (λ m≡n → inj₂ (cong succ m≡n))
  ]
  m<n∨m≡n

  where
    m<n∨m≡n : LT m n ∨ m ≡ n
    m<n∨m≡n = x<Sy→x<y∨x≡y Nm Nn (trans (sym $ <-SS m (succ n)) Sm<SSn)

x≤y→x<y∨x≡y : ∀ {m n} → N m → N n → LE m n → LT m n ∨ m ≡ n
x≤y→x<y∨x≡y = x<Sy→x<y∨x≡y

postulate
  x<y→y≡z→x<z : ∀ {m n o} → LT m n → n ≡ o → LT m o
{-# ATP prove x<y→y≡z→x<z #-}

postulate
  x≡y→y<z→x<z : ∀ {m n o} → m ≡ n → LT n o → LT m o
{-# ATP prove x≡y→y<z→x<z #-}

x≯Sy→x≯y∨x≡y : ∀ {m n} → N m → N n → NGT m (succ n) → NGT m n ∨ m ≡ succ n
x≯Sy→x≯y∨x≡y {m} {n} Nm Nn m≯Sn =
  [ (λ m<Sn → inj₁ (x≤y→x≯y Nm Nn (x<Sy→x≤y Nm Nn m<Sn)))
  , (λ m≡Sn → inj₂ m≡Sn)
  ]
  (x<Sy→x<y∨x≡y Nm (sN Nn) (x≤y→x<Sy Nm (sN Nn) (x≯y→x≤y Nm (sN Nn) m≯Sn)))

x≥y→y>0→x∸y<x : ∀ {m n} → N m → N n → GE m n → GT n zero → LT (m ∸ n) m
x≥y→y>0→x∸y<x Nm          zN          _     0>0  = ⊥-elim $ x>x→⊥ zN 0>0
x≥y→y>0→x∸y<x zN          (sN Nn)     0≥Sn  _    = ⊥-elim $ S≤0→⊥ Nn 0≥Sn
x≥y→y>0→x∸y<x (sN {m} Nm) (sN {n} Nn) Sm≥Sn Sn>0 = prf
  where
    postulate prf : LT (succ m ∸ succ n) (succ m)
    {-# ATP prove prf x∸y<Sx #-}

x<y→y≤z→x<z : ∀ {m n o} → N m → N n → N o → LT m n → LE n o → LT m o
x<y→y≤z→x<z Nm Nn No m<n n≤o =
  [ (λ n<o → <-trans Nm Nn No m<n n<o)
  , (λ n≡o → x<y→y≡z→x<z m<n n≡o)
  ] (x<Sy→x<y∨x≡y Nn No n≤o)

x≤y+x∸y : ∀ {m n} → N m → N n → LE m (n + (m ∸ n))
x≤y+x∸y {n = n} zN Nn = prf0
  where postulate prf0 : LE zero (n + (zero ∸ n))
        {-# ATP prove prf0 0≤x +-N  #-}
x≤y+x∸y (sN {m} Nm) zN = prfx0
  where postulate prfx0 : LE (succ m) (zero + (succ m ∸ zero))
        {-# ATP prove prfx0 x<Sx #-}
x≤y+x∸y (sN {m} Nm) (sN {n} Nn) = prfSS (x≤y+x∸y Nm Nn)
  where postulate prfSS : LE m (n + (m ∸ n)) →  -- IH.
                          LE (succ m) (succ n + (succ m ∸ succ n))
        {-# ATP prove prfSS x≤y→Sx≤Sy ≤-trans +-N ∸-N #-}

x∸y<x∸z→Sx∸y<Sx∸z : ∀ {m n o} → N m → N n → N o →
                    LT (m ∸ n) (m ∸ o) → LT (succ m ∸ n) (succ m ∸ o)
x∸y<x∸z→Sx∸y<Sx∸z {n = n} {o} zN Nn No 0∸n<0∸o = prf
  where
    postulate prf : LT (succ zero ∸ n) (succ zero ∸ o)
    {-# ATP prove prf ∸-0x 0<0→⊥ #-}

x∸y<x∸z→Sx∸y<Sx∸z {o = o} (sN {m} Nm) zN No Sm∸0<Sm∸o = prf
  where
    postulate prf : LT (succ (succ m) ∸ zero) (succ (succ m) ∸ o)
    {-# ATP prove prf x<x∸y→⊥ #-}

x∸y<x∸z→Sx∸y<Sx∸z (sN {m} Nm) (sN {n} Nn) zN Sm∸Sn<Sm∸0 = prf
  where
    postulate prf : LT (succ (succ m) ∸ succ n) (succ (succ m) ∸ zero)
    {-# ATP prove prf Sx∸Sy<Sx #-}

x∸y<x∸z→Sx∸y<Sx∸z (sN {m} Nm) (sN {n} Nn) (sN {o} No) Sm∸Sn<Sm∸So =
  prf (x∸y<x∸z→Sx∸y<Sx∸z Nm Nn No)
  where
    postulate
      prf : (LT (m ∸ n) (m ∸ o) → LT (succ m ∸ n) (succ m ∸ o)) →  -- IH.
            LT (succ (succ m) ∸ succ n) (succ (succ m) ∸ succ o)
    {-# ATP prove prf #-}

------------------------------------------------------------------------------
-- Properties about LT₂

postulate
  xy<00→⊥ : ∀ {m n} → N m → N n → ¬ (LT₂ m n zero zero)
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove xy<00→⊥ x<0→⊥ #-}

postulate
  Sxy₁<0y₂→⊥ : ∀ {m n₁ n₂} → N m → N n₁ → N n₂ → ¬ (LT₂ (succ m) n₁ zero n₂)
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove Sxy₁<0y₂→⊥ x<0→⊥ #-}

postulate
  0Sx<00→⊥ : ∀ {m} → N m → ¬ (LT₂ zero (succ m) zero zero)
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove 0Sx<00→⊥ x<0→⊥ #-}

postulate
  x₁y<x₂0→x₁<x₂ : ∀ {m₁ n m₂} → N m₁ → N n → N m₂ → LT₂ m₁ n m₂ zero → LT m₁ m₂
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove x₁y<x₂0→x₁<x₂ x<0→⊥ #-}

postulate
  xy₁<0y₂→x≡0∧y₁<y₂ : ∀ {m n₁ n₂} → N m → N n₁ → N n₂ → LT₂ m n₁ zero n₂ →
                      m ≡ zero ∧ LT n₁ n₂
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove xy₁<0y₂→x≡0∧y₁<y₂ x<0→⊥ #-}

[Sx∸Sy,Sy]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     LT₂ (succ m ∸ succ n) (succ n) (succ m) (succ n)
[Sx∸Sy,Sy]<[Sx,Sy] {m} {n} Nm Nn = prf
  where
    postulate prf : LT₂ (succ m ∸ succ n) (succ n) (succ m) (succ n)
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    {-# ATP prove prf x∸y<Sx #-}

[Sx,Sy∸Sx]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     LT₂ (succ m) (succ n ∸ succ m) (succ m) (succ n)
[Sx,Sy∸Sx]<[Sx,Sy] {m} {n} Nm Nn = prf
  where
    postulate prf : LT₂ (succ m) (succ n ∸ succ m) (succ m) (succ n)
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    {-# ATP prove prf x∸y<Sx #-}
