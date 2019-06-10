------------------------------------------------------------------------------
-- Properties of the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.LTC-PCF.Data.Nat.Inequalities.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.LTC-PCF.Base
open import Interactive.LTC-PCF.Base.Properties
open import Interactive.LTC-PCF.Data.Nat
open import Interactive.LTC-PCF.Data.Nat.Inequalities
open import Interactive.LTC-PCF.Data.Nat.Inequalities.EliminationProperties
open import Interactive.LTC-PCF.Data.Nat.Inequalities.ConversionRules public
open import Interactive.LTC-PCF.Data.Nat.Properties
open import Interactive.LTC-PCF.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- N.B. The elimination properties are in the module
-- LTC.Data.Nat.Inequalities.EliminationProperties.

------------------------------------------------------------------------------
-- Congruence properties

ltLeftCong : ∀ {m n o} → m ≡ n → lt m o ≡ lt n o
ltLeftCong refl = refl

ltRightCong : ∀ {m n o} → n ≡ o → lt m n ≡ lt m o
ltRightCong refl = refl

------------------------------------------------------------------------------

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

x<y→Sx<Sy : ∀ {m n} → m < n → succ₁ m < succ₁ n
x<y→Sx<Sy {m} {n} m<n = trans (lt-SS m n) m<n

Sx<Sy→x<y : ∀ {m n} → succ₁ m < succ₁ n → m < n
Sx<Sy→x<y {m} {n} Sm<Sn = trans (sym (lt-SS m n)) Sm<Sn

x≤x : ∀ {n} → N n → n ≤ n
x≤x nzero          = lt-0S zero
x≤x (nsucc {n} Nn) = trans (lt-SS n (succ₁ n)) (x≤x Nn)

x≤y→Sx≤Sy : ∀ {m n} → m ≤ n → succ₁ m ≤ succ₁ n
x≤y→Sx≤Sy {m} {n} m≤n = trans (lt-SS m (succ₁ n)) m≤n

Sx≤Sy→x≤y : ∀ {m n} → succ₁ m ≤ succ₁ n → m ≤ n
Sx≤Sy→x≤y {m} {n} Sm≤Sn = trans (sym (lt-SS m (succ₁ n))) Sm≤Sn

x≥y→x≮y : ∀ {m n} → N m → N n → m ≥ n → m ≮ n
x≥y→x≮y nzero          nzero          _     = x≮x nzero
x≥y→x≮y nzero          (nsucc Nn)     0≥Sn  = ⊥-elim (0≥S→⊥ Nn 0≥Sn)
x≥y→x≮y (nsucc {m} Nm) nzero          _     = lt-S0 m
x≥y→x≮y (nsucc {m} Nm) (nsucc {n} Nn) Sm≥Sn =
  trans (lt-SS m n) (x≥y→x≮y Nm Nn (trans (sym (lt-SS n (succ₁ m))) Sm≥Sn))

x≮y→x≥y : ∀ {m n} → N m → N n → m ≮ n → m ≥ n
x≮y→x≥y nzero nzero 0≮0 = x≤x nzero
x≮y→x≥y nzero (nsucc {n} Nn) 0≮Sn = ⊥-elim (t≢f (trans (sym (lt-0S n)) 0≮Sn))
x≮y→x≥y (nsucc {m} Nm) nzero Sm≮n = lt-0S (succ₁ m)
x≮y→x≥y (nsucc {m} Nm) (nsucc {n} Nn) Sm≮Sn =
  trans (lt-SS n (succ₁ m)) (x≮y→x≥y Nm Nn (trans (sym (lt-SS m n)) Sm≮Sn))

x>y∨x≤y : ∀ {m n} → N m → N n → m > n ∨ m ≤ n
x>y∨x≤y {n = n} nzero Nn = inj₂ (lt-0S n)
x>y∨x≤y (nsucc {m} Nm) nzero = inj₁ (lt-0S m)
x>y∨x≤y (nsucc {m} Nm) (nsucc {n} Nn) =
  case (λ m>n → inj₁ (trans (lt-SS n m) m>n))
       (λ m≤n → inj₂ (trans (lt-SS m (succ₁ n)) m≤n))
       (x>y∨x≤y Nm Nn)

x≤y→x≯y : ∀ {m n} → N m → N n → m ≤ n → m ≯ n
x≤y→x≯y nzero          Nn             _    = 0≯x Nn
x≤y→x≯y (nsucc Nm)     nzero          Sm≤0 = ⊥-elim (S≤0→⊥ Nm Sm≤0)
x≤y→x≯y (nsucc {m} Nm) (nsucc {n} Nn) Sm≤Sn =
  trans (lt-SS n m) (x≤y→x≯y Nm Nn (trans (sym (lt-SS m (succ₁ n))) Sm≤Sn))

x≯y→x≤y : ∀ {m n} → N m → N n → m ≯ n → m ≤ n
x≯y→x≤y {n = n} nzero Nn _ = lt-0S n
x≯y→x≤y (nsucc {m} Nm) nzero Sm≯0 = ⊥-elim (t≢f (trans (sym (lt-0S m)) Sm≯0))
x≯y→x≤y (nsucc {m} Nm) (nsucc {n} Nn) Sm≯Sn =
  trans (lt-SS m (succ₁ n)) (x≯y→x≤y Nm Nn (trans (sym (lt-SS n m)) Sm≯Sn))

x>y∨x≯y : ∀ {m n} → N m → N n → m > n ∨ m ≯ n
x>y∨x≯y nzero          Nn             = inj₂ (0≯x Nn)
x>y∨x≯y (nsucc {m} Nm) nzero          = inj₁ (lt-0S m)
x>y∨x≯y (nsucc {m} Nm) (nsucc {n} Nn) =
  case (λ h → inj₁ (trans (lt-SS n m) h))
       (λ h → inj₂ (trans (lt-SS n m) h))
       (x>y∨x≯y Nm Nn)

x<y∨x≥y : ∀ {m n} → N m → N n → m < n ∨ m ≥ n
x<y∨x≥y Nm Nn = x>y∨x≤y Nn Nm

x<y∨x≮y : ∀ {m n} → N m → N n → m < n ∨ m ≮ n
x<y∨x≮y Nm Nn = case (λ m<n → inj₁ m<n)
                     (λ m≥n → inj₂ (x≥y→x≮y Nm Nn m≥n))
                     (x<y∨x≥y Nm Nn)

x≡y→x≤y : ∀ {m n} → N m → N n → m ≡ n → m ≤ n
x≡y→x≤y Nm _ refl = x≤x Nm

x<y→x≤y : ∀ {m n} → N m → N n → m < n → m ≤ n
x<y→x≤y Nm             nzero          m<0   = ⊥-elim (x<0→⊥ Nm m<0)
x<y→x≤y nzero          (nsucc {n} Nn) _     = lt-0S (succ₁ n)
x<y→x≤y (nsucc {m} Nm) (nsucc {n} Nn) Sm<Sn =
  x≤y→Sx≤Sy (x<y→x≤y Nm Nn (Sx<Sy→x<y Sm<Sn))

x<Sy→x≤y : ∀ {m n} → N m → N n → m < succ₁ n → m ≤ n
x<Sy→x≤y {n = n} nzero      Nn 0<Sn  = lt-0S n
x<Sy→x≤y         (nsucc Nm) Nn Sm<Sn = Sm<Sn

x≤Sx : ∀ {m} → N m → m ≤ succ₁ m
x≤Sx Nm = x<y→x≤y Nm (nsucc Nm) (x<Sx Nm)

x<y→Sx≤y : ∀ {m n} → N m → N n → m < n → succ₁ m ≤ n
x<y→Sx≤y Nm             nzero          m<0   = ⊥-elim (x<0→⊥ Nm m<0)
x<y→Sx≤y nzero          (nsucc {n} Nn) _     = x≤y→Sx≤Sy (lt-0S n)
x<y→Sx≤y (nsucc {m} Nm) (nsucc {n} Nn) Sm<Sn =
  trans (lt-SS (succ₁ m) (succ₁ n)) Sm<Sn

Sx≤y→x<y : ∀ {m n} → N m → N n → succ₁ m ≤ n → m < n
Sx≤y→x<y Nm             nzero          Sm≤0   = ⊥-elim (S≤0→⊥ Nm Sm≤0)
Sx≤y→x<y nzero          (nsucc {n} Nn) _      = lt-0S n
Sx≤y→x<y (nsucc {m} Nm) (nsucc {n} Nn) SSm≤Sn =
  x<y→Sx<Sy (Sx≤y→x<y Nm Nn (Sx≤Sy→x≤y SSm≤Sn))

<-trans : ∀ {m n o} → N m → N n → N o → m < n → n < o → m < o
<-trans nzero          nzero           _             0<0   _    = ⊥-elim (0<0→⊥ 0<0)
<-trans nzero          (nsucc Nn)     nzero          _     Sn<0 = ⊥-elim (S<0→⊥ Sn<0)
<-trans nzero          (nsucc Nn)     (nsucc {o} No) _     _    = lt-0S o
<-trans (nsucc Nm)     Nn             nzero          _     n<0  = ⊥-elim (x<0→⊥ Nn n<0)
<-trans (nsucc Nm)     nzero          (nsucc No)     Sm<0  _    = ⊥-elim (S<0→⊥ Sm<0)
<-trans (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) Sm<Sn Sn<So =
  x<y→Sx<Sy (<-trans Nm Nn No (Sx<Sy→x<y Sm<Sn) (Sx<Sy→x<y Sn<So))

≤-trans : ∀ {m n o} → N m → N n → N o → m ≤ n → n ≤ o → m ≤ o
≤-trans {o = o} nzero Nn No _ _ = lt-0S o
≤-trans (nsucc Nm) nzero No Sm≤0 _ = ⊥-elim (S≤0→⊥ Nm Sm≤0)
≤-trans (nsucc Nm) (nsucc Nn) nzero _ Sn≤0 = ⊥-elim (S≤0→⊥ Nn Sn≤0)
≤-trans (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) Sm≤Sn Sn≤So =
  x≤y→Sx≤Sy (≤-trans Nm Nn No (Sx≤Sy→x≤y Sm≤Sn) (Sx≤Sy→x≤y Sn≤So))

x≤x+y : ∀ {m n} → N m → N n → m ≤ m + n
x≤x+y {n = n} nzero Nn = lt-0S (zero + n)
x≤x+y {n = n} (nsucc {m} Nm) Nn =
  lt (succ₁ m) (succ₁ (succ₁ m + n)) ≡⟨ lt-SS m (succ₁ m + n) ⟩
  lt m (succ₁ m + n)                 ≡⟨ ltRightCong (+-Sx m n) ⟩
  lt m (succ₁ (m + n))               ≡⟨ refl ⟩
  le m (m + n)                       ≡⟨ x≤x+y Nm Nn ⟩
  true                               ∎

x∸y<Sx : ∀ {m n} → N m → N n → m ∸ n < succ₁ m
x∸y<Sx {m} Nm nzero =
  lt (m ∸ zero) (succ₁ m) ≡⟨ ltLeftCong (∸-x0 m) ⟩
  lt m (succ₁ m)          ≡⟨ x<Sx Nm ⟩
  true                    ∎

x∸y<Sx nzero (nsucc {n} Nn) =
  lt (zero ∸ succ₁ n) [1] ≡⟨ ltLeftCong (0∸x (nsucc Nn)) ⟩
  lt zero [1]             ≡⟨ lt-0S zero ⟩
  true                    ∎

x∸y<Sx (nsucc {m} Nm) (nsucc {n} Nn) =
  lt (succ₁ m ∸ succ₁ n) (succ₁ (succ₁ m))
    ≡⟨ ltLeftCong (S∸S Nm Nn) ⟩
  lt (m ∸ n) (succ₁ (succ₁ m))
     ≡⟨ <-trans (∸-N Nm Nn) (nsucc Nm) (nsucc (nsucc Nm))
                (x∸y<Sx Nm Nn) (x<Sx (nsucc Nm))
     ⟩
  true ∎

Sx∸Sy<Sx : ∀ {m n} → N m → N n → succ₁ m ∸ succ₁ n < succ₁ m
Sx∸Sy<Sx {m} {n} Nm Nn =
  lt (succ₁ m ∸ succ₁ n) (succ₁ m) ≡⟨ ltLeftCong (S∸S Nm Nn) ⟩
  lt (m ∸ n) (succ₁ m)             ≡⟨ x∸y<Sx Nm Nn ⟩
  true                             ∎

x>y→x∸y+y≡x : ∀ {m n} → N m → N n → m > n → (m ∸ n) + n ≡ m
x>y→x∸y+y≡x nzero Nn 0>n = ⊥-elim (0>x→⊥ Nn 0>n)
x>y→x∸y+y≡x (nsucc {m} Nm) nzero Sm>0 =
  trans (+-rightIdentity (∸-N (nsucc Nm) nzero)) (∸-x0 (succ₁ m))
x>y→x∸y+y≡x (nsucc {m} Nm) (nsucc {n} Nn) Sm>Sn =
  (succ₁ m ∸ succ₁ n) + succ₁ n
    ≡⟨ +-leftCong (S∸S Nm Nn)  ⟩
  (m ∸ n) + succ₁ n
     ≡⟨ +-comm (∸-N Nm Nn) (nsucc Nn) ⟩
  succ₁ n + (m ∸ n)
    ≡⟨ +-Sx n (m ∸ n) ⟩
  succ₁ (n + (m ∸ n))
    ≡⟨ succCong (+-comm Nn (∸-N Nm Nn)) ⟩
  succ₁ ((m ∸ n) + n)
    ≡⟨ succCong (x>y→x∸y+y≡x Nm Nn (trans (sym (lt-SS n m)) Sm>Sn)) ⟩
  succ₁ m ∎

x≤y→y∸x+x≡y : ∀ {m n} → N m → N n → m ≤ n → (n ∸ m) + m ≡ n
x≤y→y∸x+x≡y {n = n} nzero Nn 0≤n =
  trans (+-rightIdentity (∸-N Nn nzero)) (∸-x0 n)
x≤y→y∸x+x≡y (nsucc Nm) nzero Sm≤0 = ⊥-elim (S≤0→⊥ Nm Sm≤0)
x≤y→y∸x+x≡y (nsucc {m} Nm) (nsucc {n} Nn) Sm≤Sn =
  (succ₁ n ∸ succ₁ m) + succ₁ m
    ≡⟨ +-leftCong (S∸S Nn Nm) ⟩
  (n ∸ m) + succ₁ m
     ≡⟨ +-comm (∸-N Nn Nm) (nsucc Nm) ⟩
  succ₁ m + (n ∸ m)
    ≡⟨ +-Sx m (n ∸ m) ⟩
  succ₁ (m + (n ∸ m))
    ≡⟨ succCong (+-comm Nm (∸-N Nn Nm)) ⟩
  succ₁ ((n ∸ m) + m)
    ≡⟨ succCong  (x≤y→y∸x+x≡y Nm Nn (trans (sym (lt-SS m (succ₁ n))) Sm≤Sn)) ⟩
  succ₁ n ∎

x<y→x<Sy : ∀ {m n} → N m → N n → m < n → m < succ₁ n
x<y→x<Sy Nm             nzero          m<0   = ⊥-elim (x<0→⊥ Nm m<0)
x<y→x<Sy nzero          (nsucc {n} Nn) 0<Sn  = lt-0S (succ₁ n)
x<y→x<Sy (nsucc {m} Nm) (nsucc {n} Nn) Sm<Sn =
  x<y→Sx<Sy (x<y→x<Sy Nm Nn (Sx<Sy→x<y Sm<Sn))

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

x<y→y≡z→x<z : ∀ {m n o} → m < n → n ≡ o → m < o
x<y→y≡z→x<z m<n refl = m<n

x≡y→y<z→x<z : ∀ {m n o} → m ≡ n → n < o → m < o
x≡y→y<z→x<z refl n<o = n<o

x≥y→y>0→x∸y<x : ∀ {m n} → N m → N n → m ≥ n → n > zero → m ∸ n < m
x≥y→y>0→x∸y<x Nm             nzero          _     0>0  = ⊥-elim (x>x→⊥ nzero 0>0)
x≥y→y>0→x∸y<x nzero          (nsucc Nn)     0≥Sn  _    = ⊥-elim (S≤0→⊥ Nn 0≥Sn)
x≥y→y>0→x∸y<x (nsucc {m} Nm) (nsucc {n} Nn) Sm≥Sn Sn>0 =
  lt (succ₁ m ∸ succ₁ n) (succ₁ m)
    ≡⟨ ltLeftCong (S∸S Nm Nn) ⟩
  lt (m ∸ n) (succ₁ m)
     ≡⟨ x∸y<Sx Nm Nn ⟩
  true ∎

------------------------------------------------------------------------------
-- Properties about LT₂

xy<00→⊥ : ∀ {m n} → N m → N n → ¬ (Lexi m n zero zero)
xy<00→⊥ Nm Nn mn<00 = case (λ m<0 → ⊥-elim (x<0→⊥ Nm m<0))
                           (λ m≡0∧n<0 → ⊥-elim (x<0→⊥ Nn (∧-proj₂ m≡0∧n<0)))
                           mn<00

0Sx<00→⊥ : ∀ {m} → ¬ (Lexi zero (succ₁ m) zero zero)
0Sx<00→⊥ 0Sm<00 = case 0<0→⊥
                       (λ 0≡0∧Sm<0 → S<0→⊥ (∧-proj₂ 0≡0∧Sm<0))
                       0Sm<00

Sxy<0y'→⊥ : ∀ {m n n'} → ¬ (Lexi (succ₁ m) n zero n')
Sxy<0y'→⊥ Smn<0n' =
  case S<0→⊥
       (λ Sm≡0∧n<n' → ⊥-elim (0≢S (sym (∧-proj₁ Sm≡0∧n<n'))))
       Smn<0n'

xy<x'0→x<x' : ∀ {m n} → N n → ∀ {m'} → Lexi m n m' zero → m < m'
xy<x'0→x<x' Nn mn<m'0 =
  case (λ m<n → m<n)
       (λ m≡n∧n<0 → ⊥-elim (x<0→⊥ Nn (∧-proj₂ m≡n∧n<0)))
       mn<m'0

xy<0y'→x≡0∧y<y' : ∀ {m} → N m → ∀ {n n'} → Lexi m n zero n' →
                  m ≡ zero ∧ n < n'
xy<0y'→x≡0∧y<y' Nm mn<0n' = case (λ m<0 → ⊥-elim (x<0→⊥ Nm m<0))
                                 (λ m≡0∧n<n' → m≡0∧n<n')
                                 mn<0n'

[Sx∸Sy,Sy]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     Lexi (succ₁ m ∸ succ₁ n) (succ₁ n) (succ₁ m) (succ₁ n)
[Sx∸Sy,Sy]<[Sx,Sy] Nm Nn = inj₁ (Sx∸Sy<Sx Nm Nn)

[Sx,Sy∸Sx]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     Lexi (succ₁ m) (succ₁ n ∸ succ₁ m) (succ₁ m) (succ₁ n)
[Sx,Sy∸Sx]<[Sx,Sy] Nm Nn = inj₂ (refl , Sx∸Sy<Sx Nn Nm)
