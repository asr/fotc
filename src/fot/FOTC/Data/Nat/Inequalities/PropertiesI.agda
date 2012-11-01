------------------------------------------------------------------------------
-- Properties of the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Inequalities.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning
open import Common.Function

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationProperties
open import FOTC.Data.Nat.PropertiesI

------------------------------------------------------------------------------
-- N.B. The elimination properties are in the module
-- FOTC.Data.Nat.Inequalities.EliminationProperties.

------------------------------------------------------------------------------
-- Congruence properties

<-leftCong : ∀ {m n o} → m ≡ n → m < o ≡ n < o
<-leftCong refl = refl

<-rightCong : ∀ {m n o} → n ≡ o → m < n ≡ m < o
<-rightCong refl = refl

------------------------------------------------------------------------------

x≥0 : ∀ {n} → N n → GE n zero
x≥0 nzero          = <-0S zero
x≥0 (nsucc {n} Nn) = <-0S (succ₁ n)

0≤x : ∀ {n} → N n → LE zero n
0≤x Nn = x≥0 Nn

0≯x : ∀ {n} → N n → NGT zero n
0≯x nzero          = <-00
0≯x (nsucc {n} Nn) = <-S0 n

x≮x : ∀ {n} → N n → NLT n n
x≮x nzero          = <-00
x≮x (nsucc {n} Nn) = trans (<-SS n n) (x≮x Nn)

Sx≰0 : ∀ {n} → N n → NLE (succ₁ n) zero
Sx≰0 nzero          = x≮x (nsucc nzero)
Sx≰0 (nsucc {n} Nn) = trans (<-SS (succ₁ n) zero) (<-S0 n)

x<Sx : ∀ {n} → N n → LT n (succ₁ n)
x<Sx nzero          = <-0S zero
x<Sx (nsucc {n} Nn) = trans (<-SS n (succ₁ n)) (x<Sx Nn)

x<y→Sx<Sy : ∀ {m n} → LT m n → LT (succ₁ m) (succ₁ n)
x<y→Sx<Sy {m} {n} m<n = trans (<-SS m n) m<n

Sx<Sy→x<y : ∀ {m n} → LT (succ₁ m) (succ₁ n) → LT m n
Sx<Sy→x<y {m} {n} Sm<Sn = trans (sym (<-SS m n)) Sm<Sn

x<y→x<Sy : ∀ {m n} → N m → N n → LT m n → LT m (succ₁ n)
x<y→x<Sy Nm             nzero          m<0   = ⊥-elim (x<0→⊥ Nm m<0)
x<y→x<Sy nzero          (nsucc {n} Nn) 0<Sn  = <-0S (succ₁ n)
x<y→x<Sy (nsucc {m} Nm) (nsucc {n} Nn) Sm<Sn =
  x<y→Sx<Sy (x<y→x<Sy Nm Nn (Sx<Sy→x<y Sm<Sn))

x≤x : ∀ {n} → N n → LE n n
x≤x nzero          = <-0S zero
x≤x (nsucc {n} Nn) = trans (<-SS n (succ₁ n)) (x≤x Nn)

x≥x : ∀ {n} → N n → GE n n
x≥x Nn = x≤x Nn

x≤y→Sx≤Sy : ∀ {m n} → LE m n → LE (succ₁ m) (succ₁ n)
x≤y→Sx≤Sy {m} {n} m≤n = trans (<-SS m (succ₁ n)) m≤n

Sx≤Sy→x≤y : ∀ {m n} → LE (succ₁ m) (succ₁ n) → LE m n
Sx≤Sy→x≤y {m} {n} Sm≤Sn = trans (sym (<-SS m (succ₁ n))) Sm≤Sn

Sx≤y→x≤y : ∀ {m n} → N m → N n → LE (succ₁ m) n → LE m n
Sx≤y→x≤y {m} {n} Nm Nn Sm≤n = x<y→x<Sy Nm Nn (trans (sym (<-SS m n)) Sm≤n)

x≰y→Sx≰Sy : ∀ m n → NLE m n → NLE (succ₁ m) (succ₁ n)
x≰y→Sx≰Sy m n m≰n = trans (<-SS m (succ₁ n)) m≰n

x>y→y<x : ∀ {m n} → N m → N n → GT m n → LT n m
x>y→y<x nzero          Nn             0>n   = ⊥-elim (0>x→⊥ Nn 0>n)
x>y→y<x (nsucc {m} Nm) nzero          _     = <-0S m
x>y→y<x (nsucc {m} Nm) (nsucc {n} Nn) Sm>Sn =
  trans (<-SS n m) (x>y→y<x Nm Nn (trans (sym (<-SS n m)) Sm>Sn))

x≥y→x≮y : ∀ {m n} → N m → N n → GE m n → NLT m n
x≥y→x≮y nzero          nzero          _     = x≮x nzero
x≥y→x≮y nzero          (nsucc Nn)     0≥Sn  = ⊥-elim (0≥S→⊥ Nn 0≥Sn)
x≥y→x≮y (nsucc {m} Nm) nzero          _     = <-S0 m
x≥y→x≮y (nsucc {m} Nm) (nsucc {n} Nn) Sm≥Sn =
  trans (<-SS m n) (x≥y→x≮y Nm Nn (trans (sym (<-SS n (succ₁ m))) Sm≥Sn))

x≮y→x≥y : ∀ {m n} → N m → N n → NLT m n → GE m n
x≮y→x≥y nzero nzero 0≮0 = x≥x nzero
x≮y→x≥y nzero (nsucc {n} Nn) 0≮Sn = ⊥-elim (true≢false (trans (sym (<-0S n)) 0≮Sn))
x≮y→x≥y (nsucc Nm) nzero Sm≮n = x≥0 (nsucc Nm)
x≮y→x≥y (nsucc {m} Nm) (nsucc {n} Nn) Sm≮Sn =
  trans (<-SS n (succ₁ m)) (x≮y→x≥y Nm Nn (trans (sym (<-SS m n)) Sm≮Sn))

x>y→x≰y : ∀ {m n} → N m → N n → GT m n → NLE m n
x>y→x≰y nzero          Nn             0>m   = ⊥-elim (0>x→⊥ Nn 0>m)
x>y→x≰y (nsucc Nm)     nzero          _     = Sx≰0 Nm
x>y→x≰y (nsucc {m} Nm) (nsucc {n} Nn) Sm>Sn =
  x≰y→Sx≰Sy m n (x>y→x≰y Nm Nn (trans (sym (<-SS n m)) Sm>Sn))

x>y∨x≤y : ∀ {m n} → N m → N n → GT m n ∨ LE m n
x>y∨x≤y nzero          Nn             = inj₂ (x≥0 Nn)
x>y∨x≤y (nsucc {m} Nm) nzero          = inj₁ (<-0S m)
x>y∨x≤y (nsucc {m} Nm) (nsucc {n} Nn) =
  case (λ m>n → inj₁ (trans (<-SS n m) m>n))
       (λ m≤n → inj₂ (x≤y→Sx≤Sy m≤n))
       (x>y∨x≤y Nm Nn)

x<y∨x≥y : ∀ {m n} → N m → N n → LT m n ∨ GE m n
x<y∨x≥y Nm Nn = x>y∨x≤y Nn Nm

x<y∨x≮y : ∀ {m n} → N m → N n → LT m n ∨ NLT m n
x<y∨x≮y Nm Nn = case (λ m<n → inj₁ m<n)
                     (λ m≥n → inj₂ (x≥y→x≮y Nm Nn m≥n))
                     (x<y∨x≥y Nm Nn)

x≤y∨x≰y : ∀ {m n} → N m → N n → LE m n ∨ NLE m n
x≤y∨x≰y nzero          Nn             = inj₁ (0≤x Nn)
x≤y∨x≰y (nsucc Nm)     nzero          = inj₂ (Sx≰0 Nm)
x≤y∨x≰y (nsucc {m} Nm) (nsucc {n} Nn) =
  case (λ m≤n → inj₁ (x≤y→Sx≤Sy m≤n))
       (λ m≰n → inj₂ (x≰y→Sx≰Sy m n m≰n))
       (x≤y∨x≰y Nm Nn)

x≡y→x≤y : ∀ {m n} → N m → N n → m ≡ n → LE m n
x≡y→x≤y {n = n} Nm Nn m≡n = subst (λ m' → LE m' n) (sym m≡n) (x≤x Nn)

x<y→x≤y : ∀ {m n} → N m → N n → LT m n → LE m n
x<y→x≤y Nm             nzero          m<0   = ⊥-elim (x<0→⊥ Nm m<0)
x<y→x≤y nzero          (nsucc {n} Nn) _     = <-0S (succ₁ n)
x<y→x≤y (nsucc {m} Nm) (nsucc {n} Nn) Sm<Sn =
  x≤y→Sx≤Sy (x<y→x≤y Nm Nn (Sx<Sy→x<y Sm<Sn))

x<Sy→x≤y : ∀ {m n} → N m → N n → LT m (succ₁ n) → LE m n
x<Sy→x≤y nzero      Nn 0<Sn  = 0≤x Nn
x<Sy→x≤y (nsucc Nm) Nn Sm<Sn = Sm<Sn

x≤y→x<Sy : ∀ {m n} → N m → N n → LE m n → LT m (succ₁ n)
x≤y→x<Sy {n = n} nzero      Nn 0≤n  = <-0S n
x≤y→x<Sy         (nsucc Nm) Nn Sm≤n = Sm≤n

x≤Sx : ∀ {m} → N m → LE m (succ₁ m)
x≤Sx Nm = x<y→x≤y Nm (nsucc Nm) (x<Sx Nm)

x<y→Sx≤y : ∀ {m n} → N m → N n → LT m n → LE (succ₁ m) n
x<y→Sx≤y Nm nzero                      m<0   = ⊥-elim (x<0→⊥ Nm m<0)
x<y→Sx≤y nzero          (nsucc {n} Nn) _     = x≤y→Sx≤Sy (0≤x Nn)
x<y→Sx≤y (nsucc {m} Nm) (nsucc {n} Nn) Sm<Sn = trans (<-SS (succ₁ m) (succ₁ n)) Sm<Sn

Sx≤y→x<y : ∀ {m n} → N m → N n → LE (succ₁ m) n → LT m n
Sx≤y→x<y Nm              nzero          Sm≤0  = ⊥-elim (S≤0→⊥ Nm Sm≤0)
Sx≤y→x<y nzero          (nsucc {n} Nn) _      = <-0S n
Sx≤y→x<y (nsucc {m} Nm) (nsucc {n} Nn) SSm≤Sn =
  x<y→Sx<Sy (Sx≤y→x<y Nm Nn (Sx≤Sy→x≤y SSm≤Sn))

x≤y→x≯y : ∀ {m n} → N m → N n → LE m n → NGT m n
x≤y→x≯y nzero          Nn             _     = 0≯x Nn
x≤y→x≯y (nsucc Nm)     nzero          Sm≤0  = ⊥-elim (S≤0→⊥ Nm Sm≤0)
x≤y→x≯y (nsucc {m} Nm) (nsucc {n} Nn) Sm≤Sn =
  trans (<-SS n m) (x≤y→x≯y Nm Nn (trans (sym (<-SS m (succ₁ n))) Sm≤Sn))

x≯y→x≤y : ∀ {m n} → N m → N n → NGT m n → LE m n
x≯y→x≤y nzero Nn _ = 0≤x Nn
x≯y→x≤y (nsucc {m} Nm) nzero Sm≯0 = ⊥-elim (true≢false (trans (sym (<-0S m)) Sm≯0))
x≯y→x≤y (nsucc {m} Nm) (nsucc {n} Nn) Sm≯Sn =
  trans (<-SS m (succ₁ n)) (x≯y→x≤y Nm Nn (trans (sym (<-SS n m)) Sm≯Sn))

Sx≯y→x≯y : ∀ {m n} → N m → N n → NGT (succ₁ m) n → NGT m n
Sx≯y→x≯y Nm Nn Sm≤n = x≤y→x≯y Nm Nn (Sx≤y→x≤y Nm Nn (x≯y→x≤y (nsucc Nm) Nn Sm≤n))

x>y∨x≯y : ∀ {m n} → N m → N n → GT m n ∨ NGT m n
x>y∨x≯y nzero          Nn             = inj₂ (0≯x Nn)
x>y∨x≯y (nsucc {m} Nm) nzero          = inj₁ (<-0S m)
x>y∨x≯y (nsucc {m} Nm) (nsucc {n} Nn) =
  case (λ h → inj₁ (trans (<-SS n m) h))
       (λ h → inj₂ (trans (<-SS n m) h))
       (x>y∨x≯y Nm Nn)

<-trans : ∀ {m n o} → N m → N n → N o → LT m n → LT n o → LT m o
<-trans nzero          nzero          _              0<0   _     = ⊥-elim (0<0→⊥ 0<0)
<-trans nzero          (nsucc Nn)     nzero          _     Sn<0  = ⊥-elim (S<0→⊥ Sn<0)
<-trans nzero          (nsucc Nn)     (nsucc {o} No) _     _     = <-0S o
<-trans (nsucc Nm)     Nn             nzero          _     n<0   = ⊥-elim (x<0→⊥ Nn n<0)
<-trans (nsucc Nm)     nzero          (nsucc No)     Sm<0  _     = ⊥-elim (S<0→⊥ Sm<0)
<-trans (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) Sm<Sn Sn<So =
  x<y→Sx<Sy (<-trans Nm Nn No (Sx<Sy→x<y Sm<Sn) (Sx<Sy→x<y Sn<So))

≤-trans : ∀ {m n o} → N m → N n → N o → LE m n → LE n o → LE m o
≤-trans nzero      Nn                 No             _     _     = 0≤x No
≤-trans (nsucc Nm) nzero              No             Sm≤0  _     = ⊥-elim (S≤0→⊥ Nm Sm≤0)
≤-trans (nsucc Nm)     (nsucc Nn)     nzero          _     Sn≤0  = ⊥-elim (S≤0→⊥ Nn Sn≤0)
≤-trans (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) Sm≤Sn Sn≤So =
  x≤y→Sx≤Sy (≤-trans Nm Nn No (Sx≤Sy→x≤y Sm≤Sn) (Sx≤Sy→x≤y Sn≤So))

pred-≤ : ∀ {n} → N n → LE (pred₁ n) n
pred-≤ nzero =
  pred₁ zero < succ₁ zero ≡⟨ <-leftCong pred-0 ⟩
  zero < succ₁ zero       ≡⟨ <-0S zero ⟩
  true ∎
pred-≤ (nsucc {n} Nn) =
  pred₁ (succ₁ n) < succ₁ (succ₁ n)
    ≡⟨ <-leftCong (pred-S n) ⟩
  n < succ₁ (succ₁ n)
    ≡⟨ <-trans Nn (nsucc Nn) (nsucc (nsucc Nn)) (x<Sx Nn) (x<Sx (nsucc Nn)) ⟩
  true ∎

x≤x+y : ∀ {m n} → N m → N n → LE m (m + n)
x≤x+y nzero Nn = x≥0 (+-N nzero Nn)
x≤x+y {n = n} (nsucc {m} Nm) Nn =
  succ₁ m < succ₁ (succ₁ m + n) ≡⟨ <-SS m (succ₁ m + n) ⟩
  m < succ₁ m + n               ≡⟨ <-rightCong (+-Sx m n) ⟩
  m < succ₁ (m + n)             ≡⟨ refl ⟩
  m ≤ m + n                     ≡⟨ x≤x+y Nm Nn ⟩
  true                          ∎

x∸y<Sx : ∀ {m n} → N m → N n → LT (m ∸ n) (succ₁ m)
x∸y<Sx {m} Nm nzero =
  m ∸ zero < succ₁ m ≡⟨ <-leftCong (∸-x0 m) ⟩
  m < succ₁ m        ≡⟨ x<Sx Nm ⟩
  true               ∎

x∸y<Sx nzero (nsucc {n} Nn) =
  zero ∸ succ₁ n < succ₁ zero ≡⟨ <-leftCong (0∸x (nsucc Nn)) ⟩
  zero < succ₁ zero           ≡⟨ <-0S zero ⟩
  true                        ∎

x∸y<Sx (nsucc {m} Nm) (nsucc {n} Nn) =
  succ₁ m ∸ succ₁ n < succ₁ (succ₁ m)
    ≡⟨ <-leftCong (S∸S Nm Nn) ⟩
  m ∸ n < succ₁ (succ₁ m)
     ≡⟨ <-trans (∸-N Nm Nn) (nsucc Nm) (nsucc (nsucc Nm))
                (x∸y<Sx Nm Nn) (x<Sx (nsucc Nm))
     ⟩
  true ∎

Sx∸Sy<Sx : ∀ {m n} → N m → N n → LT (succ₁ m ∸ succ₁ n) (succ₁ m)
Sx∸Sy<Sx {m} {n} Nm Nn =
  succ₁ m ∸ succ₁ n < succ₁ m ≡⟨ <-leftCong (S∸S Nm Nn) ⟩
  m ∸ n < succ₁ m             ≡⟨ x∸y<Sx Nm Nn ⟩
  true                        ∎

x∸Sy≤x∸y : ∀ {m n} → N m → N n → LE (m ∸ succ₁ n) (m ∸ n)
x∸Sy≤x∸y {m} {n} Nm Nn =
  m ∸ succ₁ n ≤ m ∸ n   ≡⟨ <-leftCong (∸-xS m n) ⟩
  pred₁ (m ∸ n) ≤ m ∸ n ≡⟨ pred-≤ (∸-N Nm Nn) ⟩
  true ∎

x>y→x∸y+y≡x : ∀ {m n} → N m → N n → GT m n → (m ∸ n) + n ≡ m
x>y→x∸y+y≡x nzero          Nn    0>n  = ⊥-elim (0>x→⊥ Nn 0>n)
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
    ≡⟨ succCong (x>y→x∸y+y≡x Nm Nn (trans (sym (<-SS n m)) Sm>Sn)) ⟩
  succ₁ m ∎

x≤y→y∸x+x≡y : ∀ {m n} → N m → N n → LE m n → (n ∸ m) + m ≡ n
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
    ≡⟨ succCong  (x≤y→y∸x+x≡y Nm Nn (trans (sym (<-SS m (succ₁ n))) Sm≤Sn)) ⟩
  succ₁ n ∎

x<Sy→x<y∨x≡y : ∀ {m n} → N m → N n → LT m (succ₁ n) → LT m n ∨ m ≡ n
x<Sy→x<y∨x≡y nzero nzero 0<S0 = inj₂ refl
x<Sy→x<y∨x≡y nzero (nsucc {n} Nn) 0<SSn = inj₁ (<-0S n)
x<Sy→x<y∨x≡y (nsucc {m} Nm) nzero Sm<S0 =
  ⊥-elim (x<0→⊥ Nm (trans (sym (<-SS m zero)) Sm<S0))
x<Sy→x<y∨x≡y (nsucc {m} Nm) (nsucc {n} Nn) Sm<SSn =
  case (λ m<n → inj₁ (trans (<-SS m n) m<n))
       (λ m≡n → inj₂ (succCong m≡n))
       m<n∨m≡n

  where
  m<n∨m≡n : LT m n ∨ m ≡ n
  m<n∨m≡n = x<Sy→x<y∨x≡y Nm Nn (trans (sym (<-SS m (succ₁ n))) Sm<SSn)

x≤y→x<y∨x≡y : ∀ {m n} → N m → N n → LE m n → LT m n ∨ m ≡ n
x≤y→x<y∨x≡y = x<Sy→x<y∨x≡y

x<y→y≡z→x<z : ∀ {m n o} → LT m n → n ≡ o → LT m o
x<y→y≡z→x<z {m} m<n n≡o = subst (λ n' → LT m n') n≡o m<n

x≡y→y<z→x<z : ∀ {m n o} → m ≡ n → LT n o → LT m o
x≡y→y<z→x<z {o = o} m≡n n<o = subst (λ m' → LT m' o) (sym m≡n) n<o

x≥y→y>0→x∸y<x : ∀ {m n} → N m → N n → GE m n → GT n zero → LT (m ∸ n) m
x≥y→y>0→x∸y<x Nm             nzero          _     0>0  = ⊥-elim (x>x→⊥ nzero 0>0)
x≥y→y>0→x∸y<x nzero          (nsucc Nn)     0≥Sn  _    = ⊥-elim (S≤0→⊥ Nn 0≥Sn)
x≥y→y>0→x∸y<x (nsucc {m} Nm) (nsucc {n} Nn) Sm≥Sn Sn>0 =
  (succ₁ m ∸ succ₁ n) < (succ₁ m)
    ≡⟨ <-leftCong (S∸S Nm Nn) ⟩
  (m ∸ n) < (succ₁ m)
     ≡⟨ x∸y<Sx Nm Nn ⟩
  true ∎

x<y→y≤z→x<z : ∀ {m n o} → N m → N n → N o → LT m n → LE n o → LT m o
x<y→y≤z→x<z Nm Nn No m<n n≤o = case (λ n<o → <-trans Nm Nn No m<n n<o)
                                    (λ n≡o → x<y→y≡z→x<z m<n n≡o)
                                    (x<Sy→x<y∨x≡y Nn No n≤o)

------------------------------------------------------------------------------
-- Properties about the lexicographical order

xy<00→⊥ : ∀ {m n} → N m → N n → ¬ (Lexi m n zero zero)
xy<00→⊥ Nm Nn mn<00 = case (λ m<0 → ⊥-elim (x<0→⊥ Nm m<0))
                           (λ m≡0∧n<0 → ⊥-elim (x<0→⊥ Nn (∧-proj₂ m≡0∧n<0)))
                           mn<00

0Sx<00→⊥ : ∀ {m} → ¬ (Lexi zero (succ₁ m) zero zero)
0Sx<00→⊥ 0Sm<00 = case 0<0→⊥
                       (λ 0≡0∧Sm<0 → S<0→⊥ (∧-proj₂ 0≡0∧Sm<0))
                       0Sm<00

Sxy₁<0y₂→⊥ : ∀ {m n₁ n₂} → ¬ (Lexi (succ₁ m) n₁ zero n₂)
Sxy₁<0y₂→⊥ Smn₁<0n₂ =
  case S<0→⊥
       (λ Sm≡0∧n₁<n₂ → ⊥-elim (0≢S (sym (∧-proj₁ Sm≡0∧n₁<n₂))))
       Smn₁<0n₂

x₁y<x₂0→x₁<x₂ : ∀ {m₁ n} → N n → ∀ {m₂} → Lexi m₁ n m₂ zero → LT m₁ m₂
x₁y<x₂0→x₁<x₂ Nn m₁n<m₂0 =
  case (λ m₁<n₁ → m₁<n₁)
       (λ m₁≡n₁∧n<0 → ⊥-elim (x<0→⊥ Nn (∧-proj₂ m₁≡n₁∧n<0)))
       m₁n<m₂0

xy₁<0y₂→x≡0∧y₁<y₂ : ∀ {m} → N m → ∀ {n₁ n₂} → Lexi m n₁ zero n₂ →
                    m ≡ zero ∧ LT n₁ n₂
xy₁<0y₂→x≡0∧y₁<y₂ Nm mn₁<0n₂ = case (λ m<0 → ⊥-elim (x<0→⊥ Nm m<0))
                                    (λ m≡0∧n₁<n₂ → m≡0∧n₁<n₂)
                                    mn₁<0n₂

[Sx∸Sy,Sy]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     Lexi (succ₁ m ∸ succ₁ n) (succ₁ n) (succ₁ m) (succ₁ n)
[Sx∸Sy,Sy]<[Sx,Sy] Nm Nn = inj₁ (Sx∸Sy<Sx Nm Nn)

[Sx,Sy∸Sx]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     Lexi (succ₁ m) (succ₁ n ∸ succ₁ m) (succ₁ m) (succ₁ n)
[Sx,Sy∸Sx]<[Sx,Sy] Nm Nn = inj₂ (refl , Sx∸Sy<Sx Nn Nm)
