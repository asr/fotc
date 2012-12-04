------------------------------------------------------------------------------
-- Properties of the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Inequalities.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationProperties
open import FOTC.Data.Nat.PropertiesATP

------------------------------------------------------------------------------
-- Congruence properties

ltLeftCong : ∀ {m n o} → m ≡ n → lt m o ≡ lt n o
ltLeftCong refl = refl

ltRightCong : ∀ {m n o} → n ≡ o → lt m n ≡ lt m o
ltRightCong refl = refl

------------------------------------------------------------------------------
-- N.B. The elimination properties are in the module
-- FOTC.Data.Nat.Inequalities.EliminationProperties.

x≥0 : ∀ {n} → N n → n ≥ zero
x≥0 nzero          = lt-0S zero
x≥0 (nsucc {n} Nn) = lt-0S (succ₁ n)

0≤x : ∀ {n} → N n → zero ≤ n
0≤x Nn = x≥0 Nn

0≯x : ∀ {n} → N n → zero ≯ n
0≯x nzero          = lt-00
0≯x (nsucc {n} Nn) = lt-S0 n

x≮x : ∀ {n} → N n → n ≮ n
x≮x nzero          = lt-00
x≮x (nsucc {n} Nn) = trans (lt-SS n n) (x≮x Nn)

Sx≰0 : ∀ {n} → N n → succ₁ n ≰ zero
Sx≰0 nzero          = x≮x (nsucc nzero)
Sx≰0 (nsucc {n} Nn) = trans (lt-SS (succ₁ n) zero) (lt-S0 n)

x<Sx : ∀ {n} → N n → n < succ₁ n
x<Sx nzero          = lt-0S zero
x<Sx (nsucc {n} Nn) = trans (lt-SS n (succ₁ n)) (x<Sx Nn)

postulate x<y→Sx<Sy : ∀ {m n} → m < n → succ₁ m < succ₁ n
{-# ATP prove x<y→Sx<Sy #-}

postulate Sx<Sy→x<y : ∀ {m n} → succ₁ m < succ₁ n → m < n
{-# ATP prove Sx<Sy→x<y #-}

x<y→x<Sy : ∀ {m n} → N m → N n → m < n → m < succ₁ n
x<y→x<Sy Nm             nzero          m<0   = ⊥-elim (x<0→⊥ Nm m<0)
x<y→x<Sy nzero          (nsucc {n} Nn) 0<Sn  = lt-0S (succ₁ n)
x<y→x<Sy (nsucc {m} Nm) (nsucc {n} Nn) Sm<Sn =
  x<y→Sx<Sy (x<y→x<Sy Nm Nn (Sx<Sy→x<y Sm<Sn))

x≤x : ∀ {n} → N n → n ≤ n
x≤x nzero          = lt-0S zero
x≤x (nsucc {n} Nn) = trans (lt-SS n (succ₁ n)) (x≤x Nn)

x≥x : ∀ {n} → N n → n ≥ n
x≥x Nn = x≤x Nn

x≤y→Sx≤Sy : ∀ {m n} → m ≤ n → succ₁ m ≤ succ₁ n
x≤y→Sx≤Sy {m} {n} m≤n = trans (lt-SS m (succ₁ n)) m≤n

postulate Sx≤Sy→x≤y : ∀ {m n} → succ₁ m ≤ succ₁ n → m ≤ n
{-# ATP prove Sx≤Sy→x≤y #-}

Sx≤y→x≤y : ∀ {m n} → N m → N n → succ₁ m ≤ n → m ≤ n
Sx≤y→x≤y {m} {n} Nm Nn Sm≤n = x<y→x<Sy Nm Nn (trans (sym (lt-SS m n)) Sm≤n)

x≰y→Sx≰Sy : ∀ m n → m ≰ n → succ₁ m ≰ succ₁ n
x≰y→Sx≰Sy m n m≰n = trans (lt-SS m (succ₁ n)) m≰n

x>y→y<x : ∀ {m n} → N m → N n → m > n → n < m
x>y→y<x nzero          Nn             0>n   = ⊥-elim (0>x→⊥ Nn 0>n)
x>y→y<x (nsucc {m} Nm) nzero          _     = lt-0S m
x>y→y<x (nsucc {m} Nm) (nsucc {n} Nn) Sm>Sn =
  trans (lt-SS n m) (x>y→y<x Nm Nn (trans (sym (lt-SS n m)) Sm>Sn))

x≥y→x≮y : ∀ {m n} → N m → N n → m ≥ n → m ≮ n
x≥y→x≮y nzero          nzero          _     = x≮x nzero
x≥y→x≮y nzero          (nsucc Nn)     0≥Sn  = ⊥-elim (0≥S→⊥ Nn 0≥Sn)
x≥y→x≮y (nsucc {m} Nm) nzero          _     = lt-S0 m
x≥y→x≮y (nsucc {m} Nm) (nsucc {n} Nn) Sm≥Sn =
  prf (x≥y→x≮y Nm Nn (trans (sym (lt-SS n (succ₁ m))) Sm≥Sn))
  where postulate prf : m ≮ n → succ₁ m ≮ succ₁ n
        {-# ATP prove prf #-}

x≮y→x≥y : ∀ {m n} → N m → N n → m ≮ n → m ≥ n
x≮y→x≥y nzero nzero 0≮0 = x≥x nzero
x≮y→x≥y nzero (nsucc {n} Nn) 0≮Sn =
  ⊥-elim (true≢false (trans (sym (lt-0S n)) 0≮Sn))
x≮y→x≥y (nsucc Nm) nzero Sm≮n = x≥0 (nsucc Nm)
x≮y→x≥y (nsucc {m} Nm) (nsucc {n} Nn) Sm≮Sn =
  prf (x≮y→x≥y Nm Nn (trans (sym (lt-SS m n)) Sm≮Sn))
  where postulate prf : m ≥ n → succ₁ m ≥ succ₁ n
        {-# ATP prove prf #-}

x>y→x≰y : ∀ {m n} → N m → N n → m > n → m ≰ n
x>y→x≰y nzero          Nn             0>m   = ⊥-elim (0>x→⊥ Nn 0>m)
x>y→x≰y (nsucc Nm)     nzero          _     = Sx≰0 Nm
x>y→x≰y (nsucc {m} Nm) (nsucc {n} Nn) Sm>Sn =
  x≰y→Sx≰Sy m n (x>y→x≰y Nm Nn (trans (sym (lt-SS n m)) Sm>Sn))

postulate x>y→x≤y→⊥ : ∀ {m n} → N m → N n → m > n → m ≤ n → ⊥
{-# ATP prove x>y→x≤y→⊥ x>y→x≰y #-}

x>y∨x≤y : ∀ {m n} → N m → N n → m > n ∨ m ≤ n
x>y∨x≤y nzero          Nn             = inj₂ (x≥0 Nn)
x>y∨x≤y (nsucc {m} Nm) nzero          = inj₁ (lt-0S m)
x>y∨x≤y (nsucc {m} Nm) (nsucc {n} Nn) =
  case (λ m>n → inj₁ (trans (lt-SS n m) m>n))
       (λ m≤n → inj₂ (x≤y→Sx≤Sy m≤n))
       (x>y∨x≤y Nm Nn)

x<y∨x≥y : ∀ {m n} → N m → N n → m < n ∨ m ≥ n
x<y∨x≥y Nm Nn = x>y∨x≤y Nn Nm

x<y∨x≮y : ∀ {m n} → N m → N n → m < n ∨ m ≮ n
x<y∨x≮y Nm Nn = case (λ m<n → inj₁ m<n)
                     (λ m≥n → inj₂ (x≥y→x≮y Nm Nn m≥n))
                     (x<y∨x≥y Nm Nn)

x≤y∨x≰y : ∀ {m n} → N m → N n → m ≤ n ∨ m ≰ n
x≤y∨x≰y nzero          Nn             = inj₁ (0≤x Nn)
x≤y∨x≰y (nsucc Nm)     nzero          = inj₂ (Sx≰0 Nm)
x≤y∨x≰y (nsucc {m} Nm) (nsucc {n} Nn) =
  case (λ m≤n → inj₁ (x≤y→Sx≤Sy m≤n))
       (λ m≰n → inj₂ (x≰y→Sx≰Sy m n m≰n))
       (x≤y∨x≰y Nm Nn)

x≡y→x≤y : ∀ {m n} → N m → N n → m ≡ n → m ≤ n
x≡y→x≤y {n = n} Nm Nn m≡n = subst (λ m' → m' ≤ n) (sym m≡n) (x≤x Nn)

x<y→x≤y : ∀ {m n} → N m → N n → m < n → m ≤ n
x<y→x≤y Nm             nzero          m<0   = ⊥-elim (x<0→⊥ Nm m<0)
x<y→x≤y nzero          (nsucc {n} Nn) _     = lt-0S (succ₁ n)
x<y→x≤y (nsucc {m} Nm) (nsucc {n} Nn) Sm<Sn =
  x≤y→Sx≤Sy (x<y→x≤y Nm Nn (Sx<Sy→x<y Sm<Sn))

x<Sy→x≤y : ∀ {m n} → N m → N n → m < succ₁ n → m ≤ n
x<Sy→x≤y nzero      Nn 0<Sn  = 0≤x Nn
x<Sy→x≤y (nsucc Nm) Nn Sm<Sn = Sm<Sn

x≤y→x<Sy : ∀ {m n} → N m → N n → m ≤ n → m  < succ₁ n
x≤y→x<Sy {n = n} nzero      Nn 0≤n  = lt-0S n
x≤y→x<Sy         (nsucc Nm) Nn Sm≤n = Sm≤n

x≤Sx : ∀ {m} → N m → m ≤ succ₁ m
x≤Sx Nm = x<y→x≤y Nm (nsucc Nm) (x<Sx Nm)

x<y→Sx≤y : ∀ {m n} → N m → N n → m < n → succ₁ m ≤ n
x<y→Sx≤y Nm             nzero          m<0   = ⊥-elim (x<0→⊥ Nm m<0)
x<y→Sx≤y nzero          (nsucc Nn)     0<Sn  = x≤y→Sx≤Sy (0≤x Nn)
x<y→Sx≤y (nsucc {m} Nm) (nsucc {n} Nn) Sm<Sn = trans (lt-SS (succ₁ m) (succ₁ n)) Sm<Sn

Sx≤y→x<y : ∀ {m n} → N m → N n → succ₁ m ≤ n → m < n
Sx≤y→x<y Nm             nzero          Sm≤0   = ⊥-elim (S≤0→⊥ Nm Sm≤0)
Sx≤y→x<y nzero          (nsucc {n} Nn) _      = lt-0S n
Sx≤y→x<y (nsucc {m} Nm) (nsucc {n} Nn) SSm≤Sn =
  x<y→Sx<Sy (Sx≤y→x<y Nm Nn (Sx≤Sy→x≤y SSm≤Sn))

x≤y→x≯y : ∀ {m n} → N m → N n → m ≤ n → m ≯ n
x≤y→x≯y nzero          Nn             0≤n   = 0≯x Nn
x≤y→x≯y (nsucc Nm)     nzero          Sm≤0  = ⊥-elim (S≤0→⊥ Nm Sm≤0)
x≤y→x≯y (nsucc {m} Nm) (nsucc {n} Nn) Sm≤Sn =
  prf (x≤y→x≯y Nm Nn (trans (sym (lt-SS m (succ₁ n))) Sm≤Sn))
  where postulate prf : m ≯ n → succ₁ m ≯ succ₁ n
        {-# ATP prove prf #-}

x≯y→x≤y : ∀ {m n} → N m → N n → m ≯ n → m ≤ n
x≯y→x≤y nzero Nn _ = 0≤x Nn
x≯y→x≤y (nsucc {m} Nm) nzero Sm≯0 = ⊥-elim (true≢false (trans (sym (lt-0S m)) Sm≯0))
x≯y→x≤y (nsucc {m} Nm) (nsucc {n} Nn) Sm≯Sn =
  prf (x≯y→x≤y Nm Nn (trans (sym (lt-SS n m)) Sm≯Sn))
  where postulate prf : m ≤ n → succ₁ m ≤ succ₁ n
        {-# ATP prove prf #-}

Sx≯y→x≯y : ∀ {m n} → N m → N n → succ₁ m ≯ n → m ≯ n
Sx≯y→x≯y Nm Nn Sm≤n = x≤y→x≯y Nm Nn (Sx≤y→x≤y Nm Nn (x≯y→x≤y (nsucc Nm) Nn Sm≤n))

x>y∨x≯y : ∀ {m n} → N m → N n → m > n ∨ m ≯ n
x>y∨x≯y nzero          Nn             = inj₂ (0≯x Nn)
x>y∨x≯y (nsucc {m} Nm) nzero          = inj₁ (lt-0S m)
x>y∨x≯y (nsucc {m} Nm) (nsucc {n} Nn) =
  case (λ h → inj₁ (trans (lt-SS n m) h))
       (λ h → inj₂ (trans (lt-SS n m) h))
       (x>y∨x≯y Nm Nn)

<-trans : ∀ {m n o} → N m → N n → N o → m < n → n < o → m < o
<-trans nzero          nzero          _              0<0   _     = ⊥-elim (0<0→⊥ 0<0)
<-trans nzero          (nsucc Nn)     nzero          _     Sn<0  = ⊥-elim (S<0→⊥ Sn<0)
<-trans nzero          (nsucc Nn)     (nsucc {o} No) _     _     = lt-0S o
<-trans (nsucc Nm)     Nn             nzero          _     n<0   = ⊥-elim (x<0→⊥ Nn n<0)
<-trans (nsucc Nm)     nzero          (nsucc No)     Sm<0  _     = ⊥-elim (S<0→⊥ Sm<0)
<-trans (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) Sm<Sn Sn<So =
  x<y→Sx<Sy (<-trans Nm Nn No (Sx<Sy→x<y Sm<Sn) (Sx<Sy→x<y Sn<So))

≤-trans : ∀ {m n o} → N m → N n → N o → m ≤ n → n ≤ o → m ≤ o
≤-trans nzero          Nn             No             _     _     = 0≤x No
≤-trans (nsucc Nm)     nzero          No             Sm≤0  _     = ⊥-elim (S≤0→⊥ Nm Sm≤0)
≤-trans (nsucc Nm)     (nsucc Nn)     nzero          _     Sn≤0  = ⊥-elim (S≤0→⊥ Nn Sn≤0)
≤-trans (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) Sm≤Sn Sn≤So =
  x≤y→Sx≤Sy (≤-trans Nm Nn No (Sx≤Sy→x≤y Sm≤Sn) (Sx≤Sy→x≤y Sn≤So))

pred-≤ : ∀ {n} → N n → pred₁ n ≤ n
pred-≤ nzero = prf
  where postulate prf : pred₁ zero ≤ zero
        {-# ATP prove prf #-}

pred-≤ (nsucc {n} Nn) = prf
  where postulate prf : pred₁ (succ₁ n) ≤ succ₁ n
        {-# ATP prove prf <-trans x<Sx #-}

x≤x+y : ∀ {m n} → N m → N n → m ≤ m + n
x≤x+y         nzero          Nn = x≥0 (+-N nzero Nn)
x≤x+y {n = n} (nsucc {m} Nm) Nn = prf (x≤x+y Nm Nn)
  where postulate prf : m ≤ m + n → succ₁ m ≤ succ₁ m + n
        {-# ATP prove prf #-}

x<x+Sy : ∀ {m n} → N m → N n → m < m + succ₁ n
x<x+Sy {n = n} nzero Nn = prf0
  where postulate prf0 : zero < zero + succ₁ n
        {-# ATP prove prf0 #-}
x<x+Sy {n = n} (nsucc {m} Nm) Nn = prfS (x<x+Sy Nm Nn)
  where postulate prfS : m < m + succ₁ n → succ₁ m < succ₁ m + succ₁ n
        {-# ATP prove prfS #-}

k+x<k+y→x<y : ∀ {m n k} → N m → N n → N k → k + m < k + n → m < n
k+x<k+y→x<y {m} {n} Nm Nn nzero h = prf0
  where postulate prf0 : m < n
        {-# ATP prove prf0 #-}
k+x<k+y→x<y {m} {n} Nm Nn (nsucc {k} Nk) h = k+x<k+y→x<y Nm Nn Nk prfS
  where postulate prfS : k + m < k + n
        {-# ATP prove prfS #-}

postulate x+k<y+k→x<y : ∀ {m n k} → N m → N n → N k →
                        m + k < n + k → m < n
{-# ATP prove x+k<y+k→x<y k+x<k+y→x<y +-comm #-}

x≤y→k+x≤k+y : ∀ {m n k} → N m → N n → N k → m ≤ n → k + m ≤ k + n
x≤y→k+x≤k+y {m} {n} Nm Nn nzero h = prf0
  where
  postulate prf0 : zero + m ≤ zero + n
  {-# ATP prove prf0 #-}
x≤y→k+x≤k+y {m} {n} Nm Nn (nsucc {k} Nk) h = prfS (x≤y→k+x≤k+y Nm Nn Nk h)
  where
  postulate prfS : k + m ≤ k + n → succ₁ k + m ≤ succ₁ k + n
  {-# ATP prove prfS #-}

postulate x≤y→x+k≤y+k : ∀ {m n k} → N m → N n → N k → m ≤ n → m + k ≤ n + k
{-# ATP prove x≤y→x+k≤y+k x≤y→k+x≤k+y +-comm #-}

x<y→Sx∸y≡0 : ∀ {m n} → N m → N n → m < n → succ₁ m ∸ n ≡ zero
x<y→Sx∸y≡0 Nm nzero h = ⊥-elim (x<0→⊥ Nm h)
x<y→Sx∸y≡0 nzero (nsucc {n} Nn) h = prf0S
  where postulate prf0S : succ₁ zero ∸ succ₁ n ≡ zero
        {-# ATP prove prf0S S∸S 0∸x #-}
x<y→Sx∸y≡0 (nsucc {m} Nm) (nsucc {n} Nn) h = prfSS (x<y→Sx∸y≡0 Nm Nn m<n)
  where
  postulate m<n : m < n
  {-# ATP prove m<n #-}

  postulate prfSS : succ₁ m ∸ n ≡ zero → succ₁ (succ₁ m) ∸ succ₁ n ≡ zero
  {-# ATP prove prfSS S∸S #-}

postulate x≤y→x∸y≡0 : ∀ {m n} → N m → N n → m ≤ n → m ∸ n ≡ zero
{-# ATP prove x≤y→x∸y≡0 x<y→Sx∸y≡0 S∸S #-}

x<y→0<y∸x : ∀ {m n} → N m → N n → m < n → zero < n ∸ m
x<y→0<y∸x Nm nzero h = ⊥-elim (x<0→⊥ Nm h)
x<y→0<y∸x nzero (nsucc {n} Nn) h = prf0S
  where postulate prf0S : zero < succ₁ n ∸ zero
        {-# ATP prove prf0S #-}

x<y→0<y∸x (nsucc {m} Nm) (nsucc {n} Nn) h = prfSS (x<y→0<y∸x Nm Nn m<n)
  where
  postulate m<n : m < n
  {-# ATP prove m<n #-}

  postulate prfSS : zero < n ∸ m → zero < succ₁ n ∸ succ₁ m
  {-# ATP prove prfSS S∸S #-}

0<x∸y→0<Sx∸y : ∀ {m n} → N m → N n → zero < m ∸ n → zero < succ₁ m ∸ n
0<x∸y→0<Sx∸y {m} Nm nzero h = prfx0
  where
  postulate prfx0 : zero < succ₁ m ∸ zero
  {-# ATP prove prfx0 #-}

0<x∸y→0<Sx∸y nzero (nsucc {n} Nn) h = ⊥-elim (x<0→⊥ nzero h')
  where postulate h' : zero < zero
        {-# ATP prove h' 0∸x #-}

0<x∸y→0<Sx∸y (nsucc {m} Nm) (nsucc {n} Nn) h = prfSS (0<x∸y→0<Sx∸y Nm Nn 0<m-n)
  where
  postulate 0<m-n : zero < m ∸ n
  {-# ATP prove 0<m-n S∸S #-}

  postulate prfSS : zero < succ₁ m ∸ n → zero < succ₁ (succ₁ m) ∸ succ₁ n
  {-# ATP prove prfSS <-trans S∸S #-}

x∸y<Sx : ∀ {m n} → N m → N n → m ∸ n < succ₁ m
x∸y<Sx {m} Nm nzero = prf
  where postulate prf : m ∸ zero < succ₁ m
        {-# ATP prove prf x<Sx #-}

x∸y<Sx nzero (nsucc {n} Nn) = prf
  where postulate prf : zero ∸ succ₁ n < succ₁ zero
        {-# ATP prove prf 0∸x #-}

x∸y<Sx (nsucc {m} Nm) (nsucc {n} Nn) = prf (x∸y<Sx Nm Nn)
  where postulate prf : m ∸ n < succ₁ m →
                        succ₁ m ∸ succ₁ n < succ₁ (succ₁ m)
        {-# ATP prove prf <-trans ∸-N x<Sx S∸S #-}

postulate Sx∸Sy<Sx : ∀ {m n} → N m → N n → succ₁ m ∸ succ₁ n < succ₁ m
{-# ATP prove Sx∸Sy<Sx x∸y<Sx S∸S #-}

x<x∸y→⊥ : ∀ {m n} → N m → N n → ¬ (m < m ∸ n)
x<x∸y→⊥ {m} Nm nzero m<m∸0 = prf
  where postulate prf : ⊥
        {-# ATP prove prf x<x→⊥ #-}
x<x∸y→⊥ nzero (nsucc Nn) 0<0∸Sn = prf
 where postulate prf : ⊥
       {-# ATP prove prf x<x→⊥ 0∸x #-}
x<x∸y→⊥ (nsucc Nm) (nsucc Nn) Sm<Sm∸Sn = prf
  where postulate prf : ⊥
        {-# ATP prove prf ∸-N x<y→y<x→⊥ x∸y<Sx S∸S #-}

postulate x∸Sy≤x∸y : ∀ {m n} → N m → N n → m ∸ succ₁ n ≤ m ∸ n
{-# ATP prove x∸Sy≤x∸y pred-≤ ∸-N #-}

x>y→x∸y+y≡x : ∀ {m n} → N m → N n → m > n → (m ∸ n) + n ≡ m
x>y→x∸y+y≡x nzero          Nn 0>n = ⊥-elim (0>x→⊥ Nn 0>n)
x>y→x∸y+y≡x (nsucc {m} Nm) nzero Sm>0 = prf
  where postulate prf : (succ₁ m ∸ zero) + zero ≡ succ₁ m
        {-# ATP prove prf +-rightIdentity ∸-N #-}

x>y→x∸y+y≡x (nsucc {m} Nm) (nsucc {n} Nn) Sm>Sn = prf (x>y→x∸y+y≡x Nm Nn m>n)
  where
  postulate m>n : m > n
  {-# ATP prove m>n #-}

  postulate prf : (m ∸ n) + n ≡ m → (succ₁ m ∸ succ₁ n) + succ₁ n ≡ succ₁ m
  {-# ATP prove prf +-comm ∸-N S∸S #-}

x≤y→y∸x+x≡y : ∀ {m n} → N m → N n → m ≤ n → (n ∸ m) + m ≡ n
x≤y→y∸x+x≡y {n = n} nzero Nn 0≤n = prf
  where postulate prf : (n ∸ zero) + zero ≡ n
        {-# ATP prove prf +-rightIdentity ∸-N #-}

x≤y→y∸x+x≡y (nsucc Nm) nzero Sm≤0 = ⊥-elim (S≤0→⊥ Nm Sm≤0)

x≤y→y∸x+x≡y (nsucc {m} Nm) (nsucc {n} Nn) Sm≤Sn = prf (x≤y→y∸x+x≡y Nm Nn m≤n)
  where
  postulate m≤n : m ≤ n
  {-# ATP prove m≤n #-}

  postulate prf : (n ∸ m) + m ≡ n → (succ₁ n ∸ succ₁ m) + succ₁ m ≡ succ₁ n
  {-# ATP prove prf +-comm ∸-N S∸S #-}

x<Sy→x<y∨x≡y : ∀ {m n} → N m → N n → m < succ₁ n → m < n ∨ m ≡ n
x<Sy→x<y∨x≡y nzero nzero 0<S0 = inj₂ refl
x<Sy→x<y∨x≡y nzero (nsucc {n} Nn) 0<SSn = inj₁ (lt-0S n)
x<Sy→x<y∨x≡y (nsucc {m} Nm) nzero Sm<S0 =
  ⊥-elim (x<0→⊥ Nm (trans (sym (lt-SS m zero)) Sm<S0))
x<Sy→x<y∨x≡y (nsucc {m} Nm) (nsucc {n} Nn) Sm<SSn =
  case (λ m<n → inj₁ (trans (lt-SS m n) m<n))
       (λ m≡n → inj₂ (succCong m≡n))
       m<n∨m≡n

  where
  m<n∨m≡n : m < n ∨ m ≡ n
  m<n∨m≡n = x<Sy→x<y∨x≡y Nm Nn (trans (sym (lt-SS m (succ₁ n))) Sm<SSn)

x≤y→x<y∨x≡y : ∀ {m n} → N m → N n → m ≤ n → m < n ∨ m ≡ n
x≤y→x<y∨x≡y = x<Sy→x<y∨x≡y

postulate x<y→y≡z→x<z : ∀ {m n o} → m < n → n ≡ o → m < o
{-# ATP prove x<y→y≡z→x<z #-}

postulate x≡y→y<z→x<z : ∀ {m n o} → m ≡ n → n < o → m < o
{-# ATP prove x≡y→y<z→x<z #-}

x≯Sy→x≯y∨x≡Sy : ∀ {m n} → N m → N n → m ≯ succ₁ n → m ≯ n ∨ m ≡ succ₁ n
x≯Sy→x≯y∨x≡Sy {m} {n} Nm Nn m≯Sn =
  case (λ m<Sn → inj₁ (x≤y→x≯y Nm Nn (x<Sy→x≤y Nm Nn m<Sn)))
       (λ m≡Sn → inj₂ m≡Sn)
       (x<Sy→x<y∨x≡y Nm (nsucc Nn) (x≤y→x<Sy Nm (nsucc Nn) (x≯y→x≤y Nm (nsucc Nn) m≯Sn)))

x≥y→y>0→x∸y<x : ∀ {m n} → N m → N n → m ≥ n → n > zero → m ∸ n < m
x≥y→y>0→x∸y<x Nm             nzero          _     0>0  = ⊥-elim (x>x→⊥ nzero 0>0)
x≥y→y>0→x∸y<x nzero          (nsucc Nn)     0≥Sn  _    = ⊥-elim (S≤0→⊥ Nn 0≥Sn)
x≥y→y>0→x∸y<x (nsucc {m} Nm) (nsucc {n} Nn) Sm≥Sn Sn>0 = prf
  where postulate prf : succ₁ m ∸ succ₁ n < succ₁ m
        {-# ATP prove prf x∸y<Sx 0∸x S∸S #-}

x<y→y≤z→x<z : ∀ {m n o} → N m → N n → N o → m < n → n ≤ o → m < o
x<y→y≤z→x<z Nm Nn No m<n n≤o = case (λ n<o → <-trans Nm Nn No m<n n<o)
                                    (λ n≡o → x<y→y≡z→x<z m<n n≡o)
                                    (x<Sy→x<y∨x≡y Nn No n≤o)

x≤y+x∸y : ∀ {m n} → N m → N n → m ≤ n + (m ∸ n)
x≤y+x∸y {n = n} nzero Nn = prf0
  where postulate prf0 : zero ≤ n + (zero ∸ n)
        {-# ATP prove prf0 0≤x +-N #-}
x≤y+x∸y (nsucc {m} Nm) nzero = prfx0
  where postulate prfx0 : succ₁ m ≤ zero + (succ₁ m ∸ zero)
        {-# ATP prove prfx0 x<Sx #-}
x≤y+x∸y (nsucc {m} Nm) (nsucc {n} Nn) = prfSS (x≤y+x∸y Nm Nn)
  where postulate prfSS : m ≤ n + (m ∸ n) →
                          succ₁ m ≤ succ₁ n + (succ₁ m ∸ succ₁ n)
        {-# ATP prove prfSS x≤y→Sx≤Sy ≤-trans +-N ∸-N S∸S #-}

x∸y<x∸z→Sx∸y<Sx∸z : ∀ {m n o} → N m → N n → N o →
                    m ∸ n < m ∸ o → succ₁ m ∸ n < succ₁ m ∸ o
x∸y<x∸z→Sx∸y<Sx∸z {n = n} {o} nzero Nn No 0∸n<0∸o = prf
  where postulate prf : succ₁ zero ∸ n < succ₁ zero ∸ o
        {-# ATP prove prf 0∸x 0<0→⊥ #-}

x∸y<x∸z→Sx∸y<Sx∸z {o = o} (nsucc {m} Nm) nzero No Sm∸0<Sm∸o = prf
  where postulate prf : succ₁ (succ₁ m) ∸ zero < succ₁ (succ₁ m) ∸ o
        {-# ATP prove prf x<x∸y→⊥ #-}

x∸y<x∸z→Sx∸y<Sx∸z (nsucc {m} Nm) (nsucc {n} Nn) nzero Sm∸Sn<Sm∸0 = prf
  where postulate prf : succ₁ (succ₁ m) ∸ succ₁ n < succ₁ (succ₁ m) ∸ zero
        {-# ATP prove prf Sx∸Sy<Sx #-}

x∸y<x∸z→Sx∸y<Sx∸z (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) Sm∸Sn<Sm∸So =
  prf (x∸y<x∸z→Sx∸y<Sx∸z Nm Nn No)
  where
  postulate
    prf : (m ∸ n < m ∸ o → succ₁ m ∸ n < succ₁ m ∸ o) →
          succ₁ (succ₁ m) ∸ succ₁ n < succ₁ (succ₁ m) ∸ succ₁ o
  {-# ATP prove prf S∸S #-}

------------------------------------------------------------------------------
-- Properties about the lexicographical order

postulate xy<00→⊥ : ∀ {m n} → N m → N n → ¬ (Lexi m n zero zero)
{-# ATP prove xy<00→⊥ x<0→⊥ #-}

postulate 0Sx<00→⊥ : ∀ {m} → ¬ (Lexi zero (succ₁ m) zero zero)
{-# ATP prove 0Sx<00→⊥ S<0→⊥ #-}

postulate Sxy₁<0y₂→⊥ : ∀ {m n₁ n₂} → ¬ (Lexi (succ₁ m) n₁ zero n₂)
{-# ATP prove Sxy₁<0y₂→⊥ #-}

postulate x₁y<x₂0→x₁<x₂ : ∀ {m₁ n} → N n → ∀ {m₂} → Lexi m₁ n m₂ zero → m₁ < m₂
{-# ATP prove x₁y<x₂0→x₁<x₂ x<0→⊥ #-}

postulate
  xy₁<0y₂→x≡0∧y₁<y₂ : ∀ {m} → N m → ∀ {n₁ n₂} → Lexi m n₁ zero n₂ →
                      m ≡ zero ∧ n₁ < n₂
{-# ATP prove xy₁<0y₂→x≡0∧y₁<y₂ x<0→⊥ #-}

[Sx∸Sy,Sy]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     Lexi (succ₁ m ∸ succ₁ n) (succ₁ n) (succ₁ m) (succ₁ n)
[Sx∸Sy,Sy]<[Sx,Sy] {m} {n} Nm Nn = prf
  where
  postulate prf : Lexi (succ₁ m ∸ succ₁ n) (succ₁ n) (succ₁ m) (succ₁ n)
  {-# ATP prove prf x∸y<Sx S∸S #-}

[Sx,Sy∸Sx]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     Lexi (succ₁ m) (succ₁ n ∸ succ₁ m) (succ₁ m) (succ₁ n)
[Sx,Sy∸Sx]<[Sx,Sy] {m} {n} Nm Nn = prf
  where
  postulate prf : Lexi (succ₁ m) (succ₁ n ∸ succ₁ m) (succ₁ m) (succ₁ n)
  {-# ATP prove prf x∸y<Sx S∸S #-}
