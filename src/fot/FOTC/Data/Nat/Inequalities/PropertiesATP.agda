------------------------------------------------------------------------------
-- Properties of the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Nat.Inequalities.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationPropertiesATP
open import FOTC.Data.Nat.PropertiesATP

------------------------------------------------------------------------------
-- N.B. The elimination properties are in the module
-- FOTC.Data.Nat.Inequalities.EliminationProperties.

0≯x : ∀ {n} → N n → zero ≯ n
0≯x nzero = prf
  where postulate prf : zero ≯ zero
        {-# ATP prove prf #-}
0≯x (nsucc {n} Nn) = prf
  where postulate prf : zero ≯ succ₁ n
        {-# ATP prove prf #-}

0≮x→x≡0 : ∀ {n} → N n → zero ≮ n → n ≡ zero
0≮x→x≡0 nzero h = refl
0≮x→x≡0 (nsucc {n} Nn) h = prf
  where postulate prf : succ₁ n ≡ zero
        {-# ATP prove prf #-}

x≮x : ∀ {n} → N n → n ≮ n
x≮x nzero = prf
  where postulate prf : zero ≮ zero
        {-# ATP prove prf #-}
x≮x (nsucc {n} Nn) = prf (x≮x Nn)
  where postulate prf : n ≮ n → succ₁ n ≮ succ₁ n
        {-# ATP prove prf #-}

Sx≰0 : ∀ {n} → N n → succ₁ n ≰ zero
Sx≰0 nzero = prf
  where postulate prf : succ₁ zero ≰ zero
        {-# ATP prove prf #-}
Sx≰0 (nsucc {n} Nn) = prf
  where postulate prf : succ₁ (succ₁ n) ≰ zero
        {-# ATP prove prf #-}

x<Sx : ∀ {n} → N n → n < succ₁ n
x<Sx nzero = lt-0S zero
x<Sx (nsucc {n} Nn) = prf (x<Sx Nn)
  where postulate prf : n < succ₁ n → succ₁ n < succ₁ (succ₁ n)
        {-# ATP prove prf #-}

postulate x<y→Sx<Sy : ∀ {m n} → m < n → succ₁ m < succ₁ n
{-# ATP prove x<y→Sx<Sy #-}

postulate Sx<Sy→x<y : ∀ {m n} → succ₁ m < succ₁ n → m < n
{-# ATP prove Sx<Sy→x<y #-}

x<y→x<Sy : ∀ {m n} → N m → N n → m < n → m < succ₁ n
x<y→x<Sy {m} Nm nzero h = prf
  where postulate prf : m < succ₁ zero
        {-# ATP prove prf x<0→⊥ #-}
x<y→x<Sy nzero (nsucc {n} Nn) _ = lt-0S (succ₁ n)
x<y→x<Sy (nsucc {m} Nm) (nsucc {n} Nn) h = prf (x<y→x<Sy Nm Nn m<n)
  where
  postulate m<n : m < n
  {-# ATP prove m<n #-}

  postulate prf : m < succ₁ n → succ₁ m < succ₁ (succ₁ n)
  {-# ATP prove prf #-}

x≤x : ∀ {n} → N n → n ≤ n
x≤x nzero = lt-0S zero
x≤x (nsucc {n} Nn) = prf (x≤x Nn)
  where postulate prf : n ≤ n → succ₁ n ≤ succ₁ n
        {-# ATP prove prf #-}

postulate 2*SSx≥2 : ∀ {n} → N n →
                    succ₁ (succ₁ zero) * succ₁ (succ₁ n) ≥ succ₁ (succ₁ zero)
{-# ATP prove 2*SSx≥2 #-}

postulate x≤y→Sx≤Sy : ∀ {m n} → m ≤ n → succ₁ m ≤ succ₁ n
{-# ATP prove x≤y→Sx≤Sy #-}

postulate Sx≤Sy→x≤y : ∀ {m n} → succ₁ m ≤ succ₁ n → m ≤ n
{-# ATP prove Sx≤Sy→x≤y #-}

postulate Sx≤y→x≤y : ∀ {m n} → N m → N n → succ₁ m ≤ n → m ≤ n
{-# ATP prove Sx≤y→x≤y x<y→x<Sy #-}

postulate x≰y→Sx≰Sy : ∀ m n → m ≰ n → succ₁ m ≰ succ₁ n
{-# ATP prove x≰y→Sx≰Sy #-}

x>y→y<x : ∀ {m n} → N m → N n → m > n → n < m
x>y→y<x {n = n} nzero Nn h = prf
  where postulate prf : n < zero
        {-# ATP prove prf #-}
x>y→y<x (nsucc {m} Nm) nzero _ = lt-0S m
x>y→y<x (nsucc {m} Nm) (nsucc {n} Nn) h = prf (x>y→y<x Nm Nn m>n)
  where
  postulate m>n : m > n
  {-# ATP prove m>n #-}

  postulate prf : n < m → succ₁ n < succ₁ m
  {-# ATP prove prf #-}

x≥y→x≮y : ∀ {m n} → N m → N n → m ≥ n → m ≮ n
x≥y→x≮y nzero nzero h = prf
  where postulate prf : zero ≮ zero
        {-# ATP prove prf #-}
x≥y→x≮y nzero (nsucc {n} Nn) h = prf
  where postulate prf : zero ≮ succ₁ n
        {-# ATP prove prf 0≥S→⊥ #-}
x≥y→x≮y (nsucc {m} Nm) nzero _ = lt-S0 m
x≥y→x≮y (nsucc {m} Nm) (nsucc {n} Nn) h =
  prf (x≥y→x≮y Nm Nn m≥n)
  where
  postulate m≥n : m ≥ n
  {-# ATP prove m≥n #-}

  postulate prf : m ≮ n → succ₁ m ≮ succ₁ n
  {-# ATP prove prf #-}

x≮y→x≥y : ∀ {m n} → N m → N n → m ≮ n → m ≥ n
x≮y→x≥y nzero nzero h = prf
  where postulate prf : zero ≥ zero
        {-# ATP prove prf #-}
x≮y→x≥y nzero (nsucc {n} Nn) h = prf
   where postulate prf : zero ≥ succ₁ n
         {-# ATP prove prf #-}
x≮y→x≥y (nsucc {m} Nm) nzero _ = lt-0S (succ₁ m)
x≮y→x≥y (nsucc {m} Nm) (nsucc {n} Nn) h =
  prf (x≮y→x≥y Nm Nn m≮n)
  where
  postulate m≮n : m ≮ n
  {-# ATP prove m≮n #-}
  postulate prf : m ≥ n → succ₁ m ≥ succ₁ n
  {-# ATP prove prf #-}

x>y→x≰y : ∀ {m n} → N m → N n → m > n → m ≰ n
x>y→x≰y {n = n} nzero Nn h = prf
  where postulate prf : zero ≰ n
        {-# ATP prove prf 0>x→⊥ #-}
x>y→x≰y (nsucc {m} Nm) nzero h = prf
  where postulate prf : succ₁ m ≰ zero
        {-# ATP prove prf Sx≰0 #-}
x>y→x≰y (nsucc {m} Nm) (nsucc {n} Nn) h = prf (x>y→x≰y Nm Nn m>n)
  where
  postulate m>n : m > n
  {-# ATP prove m>n #-}

  postulate prf : m ≰ n → succ₁ m ≰ succ₁ n
  {-# ATP prove prf #-}

x>y∨x≤y : ∀ {m n} → N m → N n → m > n ∨ m ≤ n
x>y∨x≤y {n = n} nzero Nn = prf
  where postulate prf : zero > n ∨ zero ≤ n
        {-# ATP prove prf #-}
x>y∨x≤y (nsucc {m} Nm) nzero = prf
  where postulate prf : succ₁ m > zero ∨ succ₁ m  ≤ zero
        {-# ATP prove prf #-}
x>y∨x≤y (nsucc {m} Nm) (nsucc {n} Nn) = prf (x>y∨x≤y Nm Nn)
  where postulate prf : m > n ∨ m ≤ n → succ₁ m > succ₁ n ∨ succ₁ m ≤ succ₁ n
        {-# ATP prove prf #-}

x<y∨x≥y : ∀ {m n} → N m → N n → m < n ∨ m ≥ n
x<y∨x≥y Nm Nn = x>y∨x≤y Nn Nm

x<y∨x≮y : ∀ {m n} → N m → N n → m < n ∨ m ≮ n
x<y∨x≮y nzero nzero = prf
  where postulate prf : zero < zero ∨ zero ≮ zero
        {-# ATP prove prf #-}
x<y∨x≮y nzero (nsucc {n} Nn) = prf
  where postulate prf : zero < succ₁ n ∨ zero ≮ succ₁ n
        {-# ATP prove prf #-}
x<y∨x≮y (nsucc {m} Nm) nzero = prf
  where postulate prf : succ₁ m < zero ∨ succ₁ m ≮ zero
        {-# ATP prove prf #-}
x<y∨x≮y (nsucc {m} Nm) (nsucc {n} Nn) = prf (x<y∨x≮y Nm Nn)
  where postulate prf : m < n ∨ m ≮ n → succ₁ m < succ₁ n ∨ succ₁ m ≮ succ₁ n
        {-# ATP prove prf #-}

x≤y∨x≰y : ∀ {m n} → N m → N n → m ≤ n ∨ m ≰ n
x≤y∨x≰y {n = n} nzero Nn = prf
  where postulate prf : zero ≤ n ∨ zero ≰ n
        {-# ATP prove prf #-}
x≤y∨x≰y (nsucc {m} Nm) nzero = prf
  where postulate prf : succ₁ m ≤ zero ∨ succ₁ m ≰ zero
        {-# ATP prove prf Sx≰0 #-}
x≤y∨x≰y (nsucc {m} Nm) (nsucc {n} Nn) = prf (x≤y∨x≰y Nm Nn)
  where postulate prf : m ≤ n ∨ m ≰ n → succ₁ m ≤ succ₁ n ∨ succ₁ m ≰ succ₁ n
        {-# ATP prove prf #-}

postulate x≡y→x≤y : ∀ {m n} → N m → N n → m ≡ n → m ≤ n
{-# ATP prove x≡y→x≤y x≤x #-}

x<y→x≤y : ∀ {m n} → N m → N n → m < n → m ≤ n
x<y→x≤y {m} Nm nzero h = prf
  where postulate prf : m ≤ zero
        {-# ATP prove prf x<0→⊥ #-}
x<y→x≤y nzero  (nsucc {n} Nn) _ = lt-0S (succ₁ n)
x<y→x≤y (nsucc {m} Nm) (nsucc {n} Nn) h = prf (x<y→x≤y Nm Nn m<n)
  where
  postulate m<n : m < n
  {-# ATP prove m<n #-}

  postulate prf : m ≤ n → succ₁ m ≤ succ₁ n
  {-# ATP prove prf #-}

x<Sy→x≤y : ∀ {m n} → N m → N n → m < succ₁ n → m ≤ n
x<Sy→x≤y {n = n} nzero      Nn _     = lt-0S n
x<Sy→x≤y         (nsucc Nm) Nn Sm<Sn = Sm<Sn

x≤y→x<Sy : ∀ {m n} → N m → N n → m ≤ n → m  < succ₁ n
x≤y→x<Sy {n = n} nzero      Nn _    = lt-0S n
x≤y→x<Sy         (nsucc Nm) Nn Sm≤n = Sm≤n

x≤Sx : ∀ {m} → N m → m ≤ succ₁ m
x≤Sx nzero = lt-0S (succ₁ zero)
x≤Sx (nsucc {m} Nm) = prf (x≤Sx Nm)
  where postulate prf : m ≤ succ₁ m → succ₁ m ≤ succ₁ (succ₁ m)
        {-# ATP prove prf #-}

x<y→Sx≤y : ∀ {m n} → N m → N n → m < n → succ₁ m ≤ n
x<y→Sx≤y {m} Nm nzero h = prf
  where postulate prf : succ₁ m ≤ zero
        {-# ATP prove prf x<0→⊥ #-}
x<y→Sx≤y nzero (nsucc {n} Nn) h = prf
  where postulate prf : succ₁ zero ≤ succ₁ n
        {-# ATP prove prf x<0→⊥ #-}
x<y→Sx≤y (nsucc {m} Nm) (nsucc {n} Nn) h = prf
  where postulate prf : succ₁ (succ₁ m) ≤ succ₁ n
        {-# ATP prove prf #-}

Sx≤y→x<y : ∀ {m n} → N m → N n → succ₁ m ≤ n → m < n
Sx≤y→x<y {m} Nm nzero h = prf
  where postulate prf : m < zero
        {-# ATP prove prf S≤0→⊥ #-}
Sx≤y→x<y nzero (nsucc {n} Nn) _  = lt-0S n
Sx≤y→x<y (nsucc {m} Nm) (nsucc {n} Nn) h = prf (Sx≤y→x<y Nm Nn Sm≤n)
  where
  postulate Sm≤n : succ₁ m ≤ n
  {-# ATP prove Sm≤n  #-}

  postulate prf : m < n → succ₁ m < succ₁ n
  {-# ATP prove prf  #-}

x≤y→x≯y : ∀ {m n} → N m → N n → m ≤ n → m ≯ n
x≤y→x≯y nzero nzero h = prf
  where postulate prf : zero ≯ zero
        {-# ATP prove prf #-}
x≤y→x≯y nzero (nsucc {n} Nn) h = prf
  where postulate prf : zero ≯ succ₁ n
        {-# ATP prove prf #-}
x≤y→x≯y (nsucc {m} Nm) nzero h = prf
  where postulate prf : succ₁ m ≯ zero
        {-# ATP prove prf S≤0→⊥ #-}
x≤y→x≯y (nsucc {m} Nm) (nsucc {n} Nn) h = prf (x≤y→x≯y Nm Nn m≤n)
  where
  postulate m≤n : m ≤ n
  {-# ATP prove m≤n #-}

  postulate prf : m ≯ n → succ₁ m ≯ succ₁ n
  {-# ATP prove prf #-}

x≯y→x≤y : ∀ {m n} → N m → N n → m ≯ n → m ≤ n
x≯y→x≤y {n = n} nzero Nn _ = lt-0S n
x≯y→x≤y (nsucc {m} Nm) nzero h = prf
  where postulate prf : succ₁ m ≤ zero
        {-# ATP prove prf #-}
x≯y→x≤y (nsucc {m} Nm) (nsucc {n} Nn) h =
  prf (x≯y→x≤y Nm Nn m≯n)
  where
  postulate m≯n : m ≯ n
  {-# ATP prove m≯n #-}

  postulate prf : m ≤ n → succ₁ m ≤ succ₁ n
  {-# ATP prove prf #-}

Sx≯y→x≯y : ∀ {m n} → N m → N n → succ₁ m ≯ n → m ≯ n
Sx≯y→x≯y nzero nzero h = prf
  where postulate prf : zero ≯ zero
        {-# ATP prove prf #-}
Sx≯y→x≯y nzero (nsucc {n} Nn) h = prf
  where postulate prf : zero ≯ succ₁ n
        {-# ATP prove prf #-}
Sx≯y→x≯y (nsucc {m} Nm) nzero h = prf
  where postulate prf : succ₁ m ≯ zero
        {-# ATP prove prf #-}
Sx≯y→x≯y (nsucc {m} Nm) (nsucc {n} Nn) h = prf (Sx≯y→x≯y Nm Nn Sm≯n)
  where
  postulate Sm≯n : succ₁ m ≯ n
  {-# ATP prove Sm≯n #-}
  postulate prf : m ≯ n → succ₁ m ≯ succ₁ n
  {-# ATP prove prf #-}

x>y∨x≯y : ∀ {m n} → N m → N n → m > n ∨ m ≯ n
x>y∨x≯y {n = n} nzero Nn = prf
  where postulate prf : zero > n ∨ zero ≯ n
        {-# ATP prove prf 0≯x #-}
x>y∨x≯y (nsucc {m} Nm) nzero = prf
  where postulate prf : succ₁ m > zero ∨ succ₁ m ≯ zero
        {-# ATP prove prf #-}
x>y∨x≯y (nsucc {m} Nm) (nsucc {n} Nn) = prf (x>y∨x≯y Nm Nn)
  where postulate prf : m > n ∨ m ≯ n →
                        succ₁ m > succ₁ n ∨ succ₁ m ≯ succ₁ n
        {-# ATP prove prf #-}

<-trans : ∀ {m n o} → N m → N n → N o → m < n → n < o → m < o
<-trans {o = o} nzero nzero No h₁ h₂ = prf
  where postulate prf : zero < o
        {-# ATP prove prf #-}
<-trans nzero (nsucc Nn) nzero h₁ h₂ = prf
  where postulate prf : zero < zero
        {-# ATP prove prf #-}
<-trans nzero (nsucc Nn) (nsucc {o} No) _ _ = lt-0S o
<-trans (nsucc {m} Nm) Nn nzero h₁ h₂ = prf
  where postulate prf : succ₁ m < zero
        {-# ATP prove prf x<0→⊥ #-}
<-trans (nsucc {m} Nm) nzero (nsucc {o} No) h₁ h₂ = prf
  where postulate prf : succ₁ m < succ₁ o
        {-# ATP prove prf #-}
<-trans (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) h₁ h₂ =
  prf (<-trans Nm Nn No m<n n<o)
  where
  postulate m<n : m < n
  {-# ATP prove m<n #-}

  postulate n<o : n < o
  {-# ATP prove n<o #-}

  postulate prf : m < o → succ₁ m < succ₁ o
  {-# ATP prove prf #-}

≤-trans : ∀ {m n o} → N m → N n → N o → m ≤ n → n ≤ o → m ≤ o
≤-trans {o = o} nzero Nn No _ _ = lt-0S o
≤-trans {o = o} (nsucc {m} Nm) nzero No h₁ h₂ = prf
  where postulate prf : succ₁ m ≤ o
        {-# ATP prove prf S≤0→⊥ #-}
≤-trans (nsucc {m} Nm) (nsucc Nn) nzero h₁ h₂ = prf
  where postulate prf : succ₁ m ≤ zero
        {-# ATP prove prf S≤0→⊥ #-}
≤-trans (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) h₁ h₂ =
  prf (≤-trans Nm Nn No m≤n n≤o)
  where
  postulate m≤n : m ≤ n
  {-# ATP prove m≤n #-}

  postulate n≤o : n ≤ o
  {-# ATP prove n≤o #-}

  postulate prf : m ≤ o → succ₁ m ≤ succ₁ o
  {-# ATP prove prf #-}

pred-≤ : ∀ {n} → N n → pred₁ n ≤ n
pred-≤ nzero = prf
  where postulate prf : pred₁ zero ≤ zero
        {-# ATP prove prf #-}
pred-≤ (nsucc {n} Nn) = prf
  where postulate prf : pred₁ (succ₁ n) ≤ succ₁ n
        {-# ATP prove prf <-trans x<Sx #-}

x≤x+y : ∀ {m n} → N m → N n → m ≤ m + n
x≤x+y {n = n} nzero          Nn = lt-0S (zero + n)
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
  where postulate prf0 : zero + m ≤ zero + n
        {-# ATP prove prf0 #-}
x≤y→k+x≤k+y {m} {n} Nm Nn (nsucc {k} Nk) h = prfS (x≤y→k+x≤k+y Nm Nn Nk h)
  where postulate prfS : k + m ≤ k + n → succ₁ k + m ≤ succ₁ k + n
        {-# ATP prove prfS #-}

postulate x≤y→x+k≤y+k : ∀ {m n k} → N m → N n → N k → m ≤ n → m + k ≤ n + k
{-# ATP prove x≤y→x+k≤y+k x≤y→k+x≤k+y +-comm #-}

x<y→Sx∸y≡0 : ∀ {m n} → N m → N n → m < n → succ₁ m ∸ n ≡ zero
x<y→Sx∸y≡0 {m} Nm nzero h = prfx0
  where postulate prfx0 : succ₁ m ∸ zero ≡ zero
        {-# ATP prove prfx0 x<0→⊥ #-}
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
x<y→0<y∸x {m} Nm nzero h = prfx0
  where postulate prfx0 : zero < zero ∸ m
        {-# ATP prove prfx0 x<0→⊥ #-}
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
  where postulate prfx0 : zero < succ₁ m ∸ zero
        {-# ATP prove prfx0 #-}
0<x∸y→0<Sx∸y nzero (nsucc {n} Nn) h = prf0S
  where postulate prf0S : zero < succ₁ zero ∸ succ₁ n
        {-# ATP prove prf0S 0∸x x<0→⊥ #-}
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
  where postulate prf : m ∸ n < succ₁ m → succ₁ m ∸ succ₁ n < succ₁ (succ₁ m)
        {-# ATP prove prf <-trans ∸-N x<Sx S∸S #-}

postulate Sx∸Sy<Sx : ∀ {m n} → N m → N n → succ₁ m ∸ succ₁ n < succ₁ m
{-# ATP prove Sx∸Sy<Sx x∸y<Sx S∸S #-}

x<x∸y→⊥ : ∀ {m n} → N m → N n → ¬ (m < m ∸ n)
x<x∸y→⊥ {m} Nm nzero h = prf
  where postulate prf : ⊥
        {-# ATP prove prf x<x→⊥ #-}
x<x∸y→⊥ nzero (nsucc Nn) h = prf
 where postulate prf : ⊥
       {-# ATP prove prf x<x→⊥ 0∸x #-}
x<x∸y→⊥ (nsucc Nm) (nsucc Nn) h = prf
  where postulate prf : ⊥
        {-# ATP prove prf ∸-N x<y→y<x→⊥ x∸y<Sx S∸S #-}

postulate x∸Sy≤x∸y : ∀ {m n} → N m → N n → m ∸ succ₁ n ≤ m ∸ n
{-# ATP prove x∸Sy≤x∸y pred-≤ ∸-N #-}

x>y→x∸y+y≡x : ∀ {m n} → N m → N n → m > n → (m ∸ n) + n ≡ m
x>y→x∸y+y≡x {n = n} nzero Nn h = prf
  where postulate prf : zero ∸ n + n ≡ zero
        {-# ATP prove prf 0>x→⊥ #-}
x>y→x∸y+y≡x (nsucc {m} Nm) nzero h = prf
  where postulate prf : (succ₁ m ∸ zero) + zero ≡ succ₁ m
        {-# ATP prove prf +-rightIdentity ∸-N #-}
x>y→x∸y+y≡x (nsucc {m} Nm) (nsucc {n} Nn) h = prf (x>y→x∸y+y≡x Nm Nn m>n)
  where
  postulate m>n : m > n
  {-# ATP prove m>n #-}

  postulate prf : (m ∸ n) + n ≡ m → (succ₁ m ∸ succ₁ n) + succ₁ n ≡ succ₁ m
  {-# ATP prove prf +-comm ∸-N S∸S #-}

x≤y→y∸x+x≡y : ∀ {m n} → N m → N n → m ≤ n → (n ∸ m) + m ≡ n
x≤y→y∸x+x≡y {n = n} nzero Nn h = prf
  where postulate prf : (n ∸ zero) + zero ≡ n
        {-# ATP prove prf +-rightIdentity ∸-N #-}
x≤y→y∸x+x≡y (nsucc {m} Nm) nzero h = prf
  where postulate prf : (zero ∸ succ₁ m) + succ₁ m ≡ zero
        {-# ATP prove prf S≤0→⊥ #-}
x≤y→y∸x+x≡y (nsucc {m} Nm) (nsucc {n} Nn) h = prf (x≤y→y∸x+x≡y Nm Nn m≤n)
  where
  postulate m≤n : m ≤ n
  {-# ATP prove m≤n #-}

  postulate prf : (n ∸ m) + m ≡ n → (succ₁ n ∸ succ₁ m) + succ₁ m ≡ succ₁ n
  {-# ATP prove prf +-comm ∸-N S∸S #-}

x<Sy→x<y∨x≡y : ∀ {m n} → N m → N n → m < succ₁ n → m < n ∨ m ≡ n
x<Sy→x<y∨x≡y nzero nzero h = inj₂ refl
x<Sy→x<y∨x≡y nzero (nsucc {n} Nn) h = inj₁ (lt-0S n)
x<Sy→x<y∨x≡y (nsucc {m} Nm) nzero h = prf
  where postulate prf : succ₁ m < zero ∨ succ₁ m ≡ zero
        {-# ATP prove prf x<0→⊥ #-}
x<Sy→x<y∨x≡y (nsucc {m} Nm) (nsucc {n} Nn) h = prf (x<Sy→x<y∨x≡y Nm Nn m<Sn)
  where
    postulate m<Sn : m < succ₁ n
    {-# ATP prove m<Sn #-}

    postulate prf : m < n ∨ m ≡ n → succ₁ m < succ₁ n ∨ succ₁ m ≡ succ₁ n
    {-# ATP prove prf #-}

x≤y→x<y∨x≡y : ∀ {m n} → N m → N n → m ≤ n → m < n ∨ m ≡ n
x≤y→x<y∨x≡y = x<Sy→x<y∨x≡y

postulate x<y→y≡z→x<z : ∀ {m n o} → m < n → n ≡ o → m < o
{-# ATP prove x<y→y≡z→x<z #-}

postulate x≡y→y<z→x<z : ∀ {m n o} → m ≡ n → n < o → m < o
{-# ATP prove x≡y→y<z→x<z #-}

x≯Sy→x≯y∨x≡Sy : ∀ {m n} → N m → N n → m ≯ succ₁ n → m ≯ n ∨ m ≡ succ₁ n
x≯Sy→x≯y∨x≡Sy nzero nzero h = prf
  where postulate prf : zero ≯ zero ∨ zero ≡ succ₁ zero
        {-# ATP prove prf #-}
x≯Sy→x≯y∨x≡Sy nzero (nsucc {n} Nn) h = prf
  where postulate prf : zero ≯ succ₁ n ∨ zero ≡ succ₁ (succ₁ n)
        {-# ATP prove prf #-}
x≯Sy→x≯y∨x≡Sy (nsucc {m} Nm) nzero h = prf
  where postulate prf : succ₁ m ≯ zero ∨ succ₁ m ≡ succ₁ zero
        {-# ATP prove prf 0≮x→x≡0 #-}
x≯Sy→x≯y∨x≡Sy (nsucc {m} Nm) (nsucc {n} Nn) h = prf (x≯Sy→x≯y∨x≡Sy Nm Nn m≯Sn)
  where
  postulate m≯Sn : m ≯ succ₁ n
  {-# ATP prove m≯Sn #-}

  postulate prf : m ≯ n ∨ m ≡ succ₁ n →
                  succ₁ m ≯ succ₁ n ∨ succ₁ m ≡ succ₁ (succ₁ n)
  {-# ATP prove prf #-}

x≥y→y>0→x∸y<x : ∀ {m n} → N m → N n → m ≥ n → n > zero → m ∸ n < m
x≥y→y>0→x∸y<x {m} Nm nzero h₁ h₂ = prf
  where postulate prf : m ∸ zero < m
        {-# ATP prove prf x∸y<Sx 0∸x S∸S #-}
x≥y→y>0→x∸y<x nzero (nsucc {n} Nn) h₁ h₂ = prf
  where postulate prf : zero ∸ succ₁ n < zero
        {-# ATP prove prf 0∸x S≤0→⊥ #-}
x≥y→y>0→x∸y<x (nsucc {m} Nm) (nsucc {n} Nn) h₁ h₂ = prf
  where postulate prf : succ₁ m ∸ succ₁ n < succ₁ m
        {-# ATP prove prf x∸y<Sx 0∸x S∸S #-}

x<y→y≤z→x<z : ∀ {m n o} → N m → N n → N o → m < n → n ≤ o → m < o
x<y→y≤z→x<z {o = o} nzero nzero No h₁ h₂ = prf
  where postulate prf : zero < o
        {-# ATP prove prf 0<0→⊥ #-}
x<y→y≤z→x<z nzero (nsucc Nn) nzero h₁ h₂ = prf
  where postulate prf : zero < zero
        {-# ATP prove prf S≤0→⊥ #-}
x<y→y≤z→x<z nzero (nsucc Nn) (nsucc {o} No) h₁ h₂ = prf
  where postulate prf : zero < succ₁ o
        {-# ATP prove prf #-}
x<y→y≤z→x<z {o = o} (nsucc {m} Nm) nzero No h₁ h₂ = prf
  where postulate prf : succ₁ m < o
        {-# ATP prove prf #-}
x<y→y≤z→x<z (nsucc {m} Nm) (nsucc Nn) nzero h₁ h₂ = prf
  where postulate prf : succ₁ m < zero
        {-# ATP prove prf S≤0→⊥ #-}
x<y→y≤z→x<z (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) h₁ h₂ =
  prf (x<y→y≤z→x<z Nm Nn No m<n n≤o)
  where
  postulate m<n : m < n
  {-# ATP prove m<n #-}

  postulate n≤o : n ≤ o
  {-# ATP prove n≤o #-}

  postulate prf : m < o → succ₁ m < succ₁ o
  {-# ATP prove prf #-}

x≤y+x∸y : ∀ {m n} → N m → N n → m ≤ n + (m ∸ n)
x≤y+x∸y {n = n} nzero Nn = prf0
  where postulate prf0 : zero ≤ n + (zero ∸ n)
        {-# ATP prove prf0 +-N #-}
x≤y+x∸y (nsucc {m} Nm) nzero = prfx0
  where postulate prfx0 : succ₁ m ≤ zero + (succ₁ m ∸ zero)
        {-# ATP prove prfx0 x<Sx #-}
x≤y+x∸y (nsucc {m} Nm) (nsucc {n} Nn) = prfSS (x≤y+x∸y Nm Nn)
  where postulate prfSS : m ≤ n + (m ∸ n) →
                          succ₁ m ≤ succ₁ n + (succ₁ m ∸ succ₁ n)
        {-# ATP prove prfSS x≤y→Sx≤Sy ≤-trans +-N ∸-N S∸S #-}

x∸y<x∸z→Sx∸y<Sx∸z : ∀ {m n o} → N m → N n → N o →
                    m ∸ n < m ∸ o → succ₁ m ∸ n < succ₁ m ∸ o
x∸y<x∸z→Sx∸y<Sx∸z {n = n} {o} nzero Nn No h = prf
  where postulate prf : succ₁ zero ∸ n < succ₁ zero ∸ o
        {-# ATP prove prf 0∸x #-}
x∸y<x∸z→Sx∸y<Sx∸z {o = o} (nsucc {m} Nm) nzero No h = prf
  where postulate prf : succ₁ (succ₁ m) ∸ zero < succ₁ (succ₁ m) ∸ o
        {-# ATP prove prf x<x∸y→⊥ #-}
x∸y<x∸z→Sx∸y<Sx∸z (nsucc {m} Nm) (nsucc {n} Nn) nzero h = prf
  where postulate prf : succ₁ (succ₁ m) ∸ succ₁ n < succ₁ (succ₁ m) ∸ zero
        {-# ATP prove prf Sx∸Sy<Sx #-}
x∸y<x∸z→Sx∸y<Sx∸z (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) h =
  prf (x∸y<x∸z→Sx∸y<Sx∸z Nm Nn No)
  where
  postulate prf : (m ∸ n < m ∸ o → succ₁ m ∸ n < succ₁ m ∸ o) →
                  succ₁ (succ₁ m) ∸ succ₁ n < succ₁ (succ₁ m) ∸ succ₁ o
  {-# ATP prove prf S∸S #-}

------------------------------------------------------------------------------
-- Properties about the lexicographical order

postulate xy<00→⊥ : ∀ {m n} → N m → N n → ¬ (Lexi m n zero zero)
{-# ATP prove xy<00→⊥ x<0→⊥ #-}

postulate 0Sx<00→⊥ : ∀ {m} → ¬ (Lexi zero (succ₁ m) zero zero)
{-# ATP prove 0Sx<00→⊥ #-}

postulate Sxy₁<0y₂→⊥ : ∀ {m n₁ n₂} → ¬ (Lexi (succ₁ m) n₁ zero n₂)
{-# ATP prove Sxy₁<0y₂→⊥ #-}

postulate x₁y<x₂0→x₁<x₂ : ∀ {m₁ n} → N n → ∀ {m₂} → Lexi m₁ n m₂ zero → m₁ < m₂
{-# ATP prove x₁y<x₂0→x₁<x₂ x<0→⊥ #-}

postulate xy₁<0y₂→x≡0∧y₁<y₂ : ∀ {m} → N m → ∀ {n₁ n₂} → Lexi m n₁ zero n₂ →
                              m ≡ zero ∧ n₁ < n₂
{-# ATP prove xy₁<0y₂→x≡0∧y₁<y₂ x<0→⊥ #-}

[Sx∸Sy,Sy]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     Lexi (succ₁ m ∸ succ₁ n) (succ₁ n) (succ₁ m) (succ₁ n)
[Sx∸Sy,Sy]<[Sx,Sy] {m} {n} Nm Nn = prf
  where postulate prf : Lexi (succ₁ m ∸ succ₁ n) (succ₁ n) (succ₁ m) (succ₁ n)
        {-# ATP prove prf x∸y<Sx S∸S #-}

[Sx,Sy∸Sx]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     Lexi (succ₁ m) (succ₁ n ∸ succ₁ m) (succ₁ m) (succ₁ n)
[Sx,Sy∸Sx]<[Sx,Sy] {m} {n} Nm Nn = prf
  where postulate prf : Lexi (succ₁ m) (succ₁ n ∸ succ₁ m) (succ₁ m) (succ₁ n)
        {-# ATP prove prf x∸y<Sx S∸S #-}
