------------------------------------------------------------------------------
-- Properties of the inequalities
------------------------------------------------------------------------------

module LTC-PCF.DataPCF.NatPCF.InequalitiesPCF.PropertiesPCF where

open import LTC.Minimal

open import LTC-PCF.DataPCF.NatPCF using
  ( _+_ ; _-_
  ; N ; sN ; zN  -- The LTC natural numbers type.
  )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF using
  ( _<_
  ; GE ; GT ; LE ; LT ; NLT
  ; LT₂
  )
open import LTC-PCF.DataPCF.NatPCF.PropertiesPCF using
  ( +-N ; minus-N
  ; +-Sx
  ; +-comm
  ; +-rightIdentity
  ; minus-0S ; minus-SS ; minus-x0
  )

open import LTC.Relation.Equalities.Properties using ( x≡y→Sx≡Sy )

open import MyStdLib.Function using ( _$_ )

------------------------------------------------------------------------------

postulate
  <-00 : NLT zero zero
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout (180).
{-# ATP prove <-00 #-}

postulate
  <-0S : (d : D) → LT zero (succ d)
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout (180).
{-# ATP prove <-0S #-}

postulate
  <-S0 : (d : D) → NLT (succ d) zero
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout (180).
{-# ATP prove <-S0 #-}

postulate
  <-SS : (d e : D) → succ d < succ e ≡ d < e
{-# ATP prove <-SS #-}

x≥0 : {n : D} → N n → GE n zero
x≥0 zN          = <-0S zero
x≥0 (sN {n} Nn) = <-0S (succ n)

0≤x : {n : D} → N n → LE zero n
0≤x Nn = x≥0 Nn

¬x<0 : {n : D} → N n → ¬ (LT n zero)
¬x<0 zN 0<0 = ⊥-elim prf
  where
    postulate prf : ⊥
    {-# ATP prove prf <-00 #-}
¬x<0 (sN Nn) Sn<0 = ⊥-elim prf
  where
    postulate prf : ⊥
    {-# ATP prove prf <-S0 #-}

postulate
  ¬0>x : {n : D} → N n → ¬ (GT zero n)
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout (180).
{-# ATP prove ¬0>x x≥0 #-}

x≰x : {n : D} → N n → NLT n n
x≰x zN          = <-00
x≰x (sN {n} Nn) = trans (<-SS n n) (x≰x Nn)

postulate
  ¬S≤0 : {d : D} → ¬ (LE (succ d) zero)
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout (180).
{-# ATP prove ¬S≤0 <-0S #-}

¬0≥S : {n : D} → N n → ¬ (GE zero (succ n))
¬0≥S Nn 0≥Sn = ¬S≤0 0≥Sn

x<Sx : {n : D} → N n → LT n (succ n)
x<Sx zN          = <-0S zero
x<Sx (sN {n} Nn) = prf (x<Sx Nn)
  where
    postulate prf : LT n (succ n) → LT (succ n) (succ (succ n))
    {-# ATP prove prf <-SS #-}

¬x<x : {m : D} → N m → ¬ (LT m m)
¬x<x zN _ = ⊥-elim prf
  where
    postulate prf : ⊥
    {-# ATP prove prf <-00 #-}
¬x<x (sN {m} Nm) _ = ⊥-elim (prf (¬x<x Nm))
  where
    postulate prf : ¬ (LT m m) → ⊥
    {-# ATP prove prf <-SS #-}

¬x>x : {m : D} → N m → ¬ (GT m m)
¬x>x Nm = ¬x<x Nm

x≤x : {m : D} → N m → LE m m
x≤x zN          = <-0S zero
x≤x (sN {m} Nm) = prf (x≤x Nm)
  where
    postulate prf : LE m m → LE (succ m) (succ m)
    {-# ATP prove prf <-SS #-}

x≥y→x≮y : {m n : D} → N m → N n → GE m n → NLT m n
x≥y→x≮y zN          zN          _     = x≰x zN
x≥y→x≮y zN          (sN Nn)     0≥Sn  = ⊥-elim (¬0≥S Nn 0≥Sn)
x≥y→x≮y (sN {m} Nm) zN          _     = <-S0 m
x≥y→x≮y (sN {m} Nm) (sN {n} Nn) Sm≥Sn =
  trans (<-SS m n) (x≥y→x≮y Nm Nn (trans (sym (<-SS n (succ m))) Sm≥Sn))

x>y∨x≤y : {m n : D} → N m → N n → GT m n ∨ LE m n
x>y∨x≤y zN          Nn          = inj₂ $ x≥0 Nn
x>y∨x≤y (sN {m} Nm) zN          = inj₁ $ <-0S m
x>y∨x≤y (sN {m} Nm) (sN {n} Nn) = prf $ x>y∨x≤y Nm Nn
  where
    postulate
      prf : (GT m n) ∨ (LE m n) →
            GT (succ m) (succ n) ∨ LE (succ m) (succ n)
    {-# ATP prove prf <-SS #-}

x<y∨x≥y : {m n : D} → N m → N n → LT m n ∨ GE m n
x<y∨x≥y Nm Nn = x>y∨x≤y Nn Nm

x≡y→x≤y : {m n : D} → {Nm : N m} → {Nn : N n} → m ≡ n → LE m n
x≡y→x≤y {Nm = Nm} refl = x≤x Nm

x<y→x≤y : {m n : D} → N m → N n → LT m n → LE m n
x<y→x≤y Nm zN          m<0            = ⊥-elim (¬x<0 Nm m<0)
x<y→x≤y zN (sN {n} Nn)          _     = <-0S (succ n)
x<y→x≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn = prf (x<y→x≤y Nm Nn m<n)
  where
    postulate m<n : LT m n
    {-# ATP prove m<n <-SS #-}

    postulate prf : LE m n →
                    LE (succ m) (succ n)
    {-# ATP prove prf <-SS #-}

x<y→Sx≤y : {m n : D} → N m → N n → LT m n → LE (succ m) n
x<y→Sx≤y Nm zN m<0 = ⊥-elim (¬x<0 Nm m<0)

x<y→Sx≤y zN (sN {n} Nn) 0<Sn = S0≤SN
  where
    postulate S0≤SN : LE (succ zero) (succ n)
    -- Equinox 5.0alpha (2010-03-29) no-success due to timeout (180).
    {-# ATP prove S0≤SN #-}

x<y→Sx≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn = prf (x<y→Sx≤y Nm Nn m<n)
  where
    postulate m<n : LT m n
    {-# ATP prove m<n <-SS #-}

    postulate prf : LE (succ m) n → LE (succ (succ m)) (succ n)
    {-# ATP prove prf <-SS #-}

Sx≤y→x<y : {m n : D} → N m → N n → LE (succ m) n → LT m n
Sx≤y→x<y Nm          zN          Sm≤0   = ⊥-elim (¬S≤0 Sm≤0)
Sx≤y→x<y zN          (sN {n} Nn) _      = <-0S n
Sx≤y→x<y (sN {m} Nm) (sN {n} Nn) SSm≤Sn = prf (Sx≤y→x<y Nm Nn Sm≤n)
  where
    postulate Sm≤n : LE (succ m) n
    {-# ATP prove Sm≤n <-SS #-}

    postulate prf : LT m n → LT (succ m) (succ n)
    {-# ATP prove prf <-SS #-}

<-trans : {m n o : D} → N m → N n → N o → LT m n → LT n o → LT m o
<-trans zN          zN           _          0<0   _    = ⊥-elim (¬x<0 zN 0<0)
<-trans zN          (sN Nn)     zN          _     Sn<0 = ⊥-elim (¬x<0 (sN Nn) Sn<0)
<-trans zN          (sN Nn)     (sN {o} No) _     _    = <-0S o
<-trans (sN Nm)     Nn          zN          _     n<0  = ⊥-elim (¬x<0 Nn n<0)
<-trans (sN Nm)     zN          (sN No)     Sm<0  _    = ⊥-elim (¬x<0 (sN Nm) Sm<0)
<-trans (sN {m} Nm) (sN {n} Nn) (sN {o} No) Sm<Sn Sn<So =
  prf (<-trans Nm Nn No m<n n<o)

  where
    postulate prf : LT m o → LT (succ m) (succ o)
    {-# ATP prove prf <-SS #-}

    postulate m<n : LT m n
    {-# ATP prove m<n <-SS #-}

    postulate n<o : LT n o
    {-# ATP prove n<o <-SS #-}

≤-trans : {m n o : D} → N m → N n → N o → LE m n → LE n o → LE m o
≤-trans zN      Nn              No          _     _     = 0≤x No
≤-trans (sN Nm) zN              No          Sm≤0  _     = ⊥-elim (¬S≤0 Sm≤0)
≤-trans (sN Nm) (sN Nn)         zN          _     Sn≤0  = ⊥-elim (¬S≤0 Sn≤0)
≤-trans (sN {m} Nm) (sN {n} Nn) (sN {o} No) Sm≤Sn Sn≤So =
  prf (≤-trans Nm Nn No m≤n n≤o)
    where
      postulate m≤n : LE m n
      {-# ATP prove m≤n <-SS #-}

      postulate n≤o : LE n o
      {-# ATP prove n≤o <-SS #-}

      postulate prf : LE m o → LE (succ m) (succ o)
      {-# ATP prove prf <-SS #-}

postulate
  Sx≤Sy→x≤y : {m n : D} → LE (succ m) (succ n) → LE m n
{-# ATP prove Sx≤Sy→x≤y <-SS #-}

x≤x+y : {m n : D} → N m → N n → LE m (m + n)
x≤x+y         zN          Nn = x≥0 (+-N zN Nn)
x≤x+y {n = n} (sN {m} Nm) Nn = prf (x≤x+y Nm Nn)
  where
    postulate prf : LE m (m + n) → LE (succ m) (succ m + n)
    {-# ATP prove prf +-Sx <-SS #-}

x-y<Sx : {m n : D} → N m → N n → LT (m - n) (succ m)
x-y<Sx {m} Nm zN = prf
  where
    postulate prf : LT (m - zero) (succ m)
    {-# ATP prove prf x<Sx minus-x0 #-}

x-y<Sx zN (sN {n} Nn) = prf
  where
    postulate prf : LT (zero - succ n) (succ zero)
    {-# ATP prove prf minus-0S minus-0S <-0S #-}

x-y<Sx (sN {m} Nm) (sN {n} Nn) = prf (x-y<Sx Nm Nn)
  where
    postulate prf : LT (m - n) (succ m) →
                    LT (succ m - succ n) (succ (succ m))
    {-# ATP prove prf <-trans minus-N x<Sx sN minus-SS #-}

postulate
  Sx-Sy<Sx : {m n : D} → N m → N n → LT (succ m - succ n) (succ m)
{-# ATP prove Sx-Sy<Sx minus-SS x-y<Sx #-}

x>y→x-y+y≡x : {m n : D} → N m → N n → GT m n → (m - n) + n ≡ m
x>y→x-y+y≡x zN Nn 0>n = ⊥-elim (¬0>x Nn 0>n)
x>y→x-y+y≡x (sN {m} Nm) zN Sm>0 = prf
  where
    postulate prf : (succ m - zero) + zero ≡ succ m
    {-# ATP prove prf +-rightIdentity minus-N sN zN minus-x0 #-}

x>y→x-y+y≡x (sN {m} Nm) (sN {n} Nn) Sm>Sn = prf (x>y→x-y+y≡x Nm Nn m>n)
  where
    postulate m>n : GT m n
    {-# ATP prove m>n <-SS #-}

    postulate prf : (m - n) + n ≡ m →
                    (succ m - succ n) + succ n ≡ succ m
    {-# ATP prove prf +-comm minus-N sN +-Sx minus-SS <-SS #-}

x≤y→y-x+x≡y : {m n : D} → N m → N n → LE m n → (n - m) + m ≡ n
x≤y→y-x+x≡y {n = n} zN Nn 0≤n  = prf
  where
    postulate prf : (n - zero) + zero ≡ n
    {-# ATP prove prf +-rightIdentity minus-N minus-x0 <-SS #-}

x≤y→y-x+x≡y (sN Nm) zN Sm≤0 = ⊥-elim (¬S≤0 Sm≤0)

x≤y→y-x+x≡y (sN {m} Nm) (sN {n} Nn) Sm≤Sn = prf (x≤y→y-x+x≡y Nm Nn m≤n)
  where
    postulate m≤n : LE m n
    {-# ATP prove m≤n <-SS #-}

    postulate prf : (n - m) + m ≡ n →
                    (succ n - succ m) + succ m ≡ succ n
    {-# ATP prove prf +-comm minus-N sN +-Sx minus-SS <-SS #-}

x<y→x<Sy : {m n : D} → N m → N n → LT m n → LT m (succ n)
x<y→x<Sy Nm          zN          m<0   = ⊥-elim (¬x<0 Nm m<0)
x<y→x<Sy zN          (sN {n} Nn) 0<Sn  = <-0S (succ n)
x<y→x<Sy (sN {m} Nm) (sN {n} Nn) Sm<Sn = prf (x<y→x<Sy Nm Nn m<n)
  where
    postulate m<n : LT m n
    {-# ATP prove m<n <-SS #-}

    postulate prf : LT m (succ n) → LT (succ m) (succ (succ n))
    {-# ATP prove prf <-SS #-}

x<Sy→x<y∨x≡y : {m n : D} → N m → N n → LT m (succ n) → LT m n ∨ m ≡ n
x<Sy→x<y∨x≡y zN zN 0<S0 = inj₂ refl
x<Sy→x<y∨x≡y zN (sN {n} Nn) 0<SSn = inj₁ (<-0S n)
x<Sy→x<y∨x≡y (sN {m} Nm) zN Sm<S0 =
  ⊥-elim (¬x<0 Nm (trans (sym (<-SS m zero)) Sm<S0))
x<Sy→x<y∨x≡y (sN {m} Nm) (sN {n} Nn) Sm<SSn =
  [ (λ m<n → inj₁ (trans (<-SS m n) m<n))
  , (λ m≡n → inj₂ (x≡y→Sx≡Sy m≡n))
  ]
  m<n∨m≡n

  where
    m<n∨m≡n : LT m n ∨ m ≡ n
    m<n∨m≡n = x<Sy→x<y∨x≡y Nm Nn (trans (sym (<-SS m (succ n))) Sm<SSn)

postulate
  x<y→y≡z→x<z : {m n o : D} → N m → N n → N o → LT m n → n ≡ o → LT m o
{-# ATP prove x<y→y≡z→x<z #-}

postulate
  x≡y→y<z→x<z : {m n o : D} → N m → N n → N o → m ≡ n → LT n o → LT m o
{-# ATP prove x≡y→y<z→x<z #-}

x≥y→y>0→x-y<x : {m n : D} → N m → N n → GE m n → GT n zero → LT (m - n) m
x≥y→y>0→x-y<x Nm          zN          _     0>0  = ⊥-elim (¬x>x zN 0>0)
x≥y→y>0→x-y<x zN          (sN Nn)     0≥Sn  _    = ⊥-elim (¬S≤0 0≥Sn)
x≥y→y>0→x-y<x (sN {m} Nm) (sN {n} Nn) Sm≥Sn Sn>0 = prf
  where
    postulate prf : LT (succ m - succ n) (succ m)
    {-# ATP prove prf minus-SS x-y<Sx #-}

------------------------------------------------------------------------------
-- Properties about LT₂

postulate
  ¬xy<00 : {m n : D} → N m → N n → ¬ (LT₂ m n zero zero)
{-# ATP prove ¬xy<00 ¬x<0 #-}

postulate
  ¬Sxy₁<0y₂ : {m n₁ n₂ : D} → N m → N n₁ → N n₂ → ¬ (LT₂ (succ m) n₁ zero n₂)
{-# ATP prove ¬Sxy₁<0y₂ ¬x<0 sN #-}

postulate
  ¬0Sx<00 : {m : D} → N m → ¬ (LT₂ zero (succ m) zero zero)
-- Equinox 5.0alpha (2010-03-29) no-success due to timeout (180).
{-# ATP prove ¬0Sx<00 ¬x<0 sN #-}

postulate
  x₁y<x₂0→x₁<x₂ : {m₁ n m₂ : D} → N m₁ → N n → N m₂ → LT₂ m₁ n m₂ zero →
                  LT m₁ m₂
{-# ATP prove x₁y<x₂0→x₁<x₂ ¬x<0 #-}

postulate
  xy₁<0y₂→x≡0∧y₁<y₂ : {m n₁ n₂ : D} → N m → N n₁ → N n₂ → LT₂ m n₁ zero n₂ →
                      m ≡ zero ∧ LT n₁ n₂
{-# ATP prove xy₁<0y₂→x≡0∧y₁<y₂ ¬x<0 #-}

[Sx-Sy,Sy]<[Sx,Sy] :
  {m n : D} → N m → N n →
  LT₂ (succ m - succ n) (succ n) (succ m) (succ n)
[Sx-Sy,Sy]<[Sx,Sy] {m} {n} Nm Nn = prf
  where
    postulate prf : LT₂ (succ m - succ n) (succ n) (succ m) (succ n)
    {-# ATP prove prf sN Sx-Sy<Sx #-}

[Sx,Sy-Sx]<[Sx,Sy] : {m n : D} → N m → N n →
                     LT₂ (succ m) (succ n - succ m) (succ m) (succ n)
[Sx,Sy-Sx]<[Sx,Sy] {m} {n} Nm Nn = prf
  where
    postulate prf : LT₂ (succ m) (succ n - succ m) (succ m) (succ n)
    {-# ATP prove prf sN Sx-Sy<Sx #-}
