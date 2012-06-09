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

x≥0 : ∀ {n} → N n → GE n zero
x≥0 zN          = <-0S zero
x≥0 (sN {n} Nn) = <-0S $ succ₁ n

0≤x : ∀ {n} → N n → LE zero n
0≤x Nn = x≥0 Nn

0≯x : ∀ {n} → N n → NGT zero n
0≯x zN          = <-00
0≯x (sN {n} Nn) = <-S0 n

x≮x : ∀ {n} → N n → NLT n n
x≮x zN          = <-00
x≮x (sN {n} Nn) = trans (<-SS n n) (x≮x Nn)

Sx≰0 : ∀ {n} → N n → NLE (succ₁ n) zero
Sx≰0 zN          = x≮x (sN zN)
Sx≰0 (sN {n} Nn) = trans (<-SS (succ₁ n) zero) (<-S0 n)

x<Sx : ∀ {n} → N n → LT n (succ₁ n)
x<Sx zN          = <-0S zero
x<Sx (sN {n} Nn) = trans (<-SS n (succ₁ n)) (x<Sx Nn)

x<y→Sx<Sy : ∀ {m n} → LT m n → LT (succ₁ m) (succ₁ n)
x<y→Sx<Sy {m} {n} m<n = trans (<-SS m n) m<n

Sx<Sy→x<y : ∀ {m n} → LT (succ₁ m) (succ₁ n) → LT m n
Sx<Sy→x<y {m} {n} Sm<Sn = trans (sym $ <-SS m n) Sm<Sn

x<y→x<Sy : ∀ {m n} → N m → N n → LT m n → LT m (succ₁ n)
x<y→x<Sy Nm          zN          m<0   = ⊥-elim $ x<0→⊥ Nm m<0
x<y→x<Sy zN          (sN {n} Nn) 0<Sn  = <-0S $ succ₁ n
x<y→x<Sy (sN {m} Nm) (sN {n} Nn) Sm<Sn =
  x<y→Sx<Sy (x<y→x<Sy Nm Nn (Sx<Sy→x<y Sm<Sn))

x≤x : ∀ {n} → N n → LE n n
x≤x zN          = <-0S zero
x≤x (sN {n} Nn) = trans (<-SS n (succ₁ n)) (x≤x Nn)

x≥x : ∀ {n} → N n → GE n n
x≥x Nn = x≤x Nn

x≤y→Sx≤Sy : ∀ {m n} → LE m n → LE (succ₁ m) (succ₁ n)
x≤y→Sx≤Sy {m} {n} m≤n = trans (<-SS m (succ₁ n)) m≤n

Sx≤Sy→x≤y : ∀ {m n} → LE (succ₁ m) (succ₁ n) → LE m n
Sx≤Sy→x≤y {m} {n} Sm≤Sn = trans (sym $ <-SS m (succ₁ n)) Sm≤Sn

Sx≤y→x≤y : ∀ {m n} → N m → N n → LE (succ₁ m) n → LE m n
Sx≤y→x≤y {m} {n} Nm Nn Sm≤n = x<y→x<Sy Nm Nn (trans (sym (<-SS m n)) Sm≤n)

x≰y→Sx≰Sy : ∀ m n → NLE m n → NLE (succ₁ m) (succ₁ n)
x≰y→Sx≰Sy m n m≰n = trans (<-SS m (succ₁ n)) m≰n

x>y→y<x : ∀ {m n} → N m → N n → GT m n → LT n m
x>y→y<x zN          Nn          0>n   = ⊥-elim $ 0>x→⊥ Nn 0>n
x>y→y<x (sN {m} Nm) zN          _     = <-0S m
x>y→y<x (sN {m} Nm) (sN {n} Nn) Sm>Sn =
  trans (<-SS n m) (x>y→y<x Nm Nn (trans (sym $ <-SS n m) Sm>Sn))

x≥y→x≮y : ∀ {m n} → N m → N n → GE m n → NLT m n
x≥y→x≮y zN          zN          _     = x≮x zN
x≥y→x≮y zN          (sN Nn)     0≥Sn  = ⊥-elim $ 0≥S→⊥ Nn 0≥Sn
x≥y→x≮y (sN {m} Nm) zN          _     = <-S0 m
x≥y→x≮y (sN {m} Nm) (sN {n} Nn) Sm≥Sn =
  trans (<-SS m n) (x≥y→x≮y Nm Nn (trans (sym $ <-SS n (succ₁ m)) Sm≥Sn))

x≮y→x≥y : ∀ {m n} → N m → N n → NLT m n → GE m n
x≮y→x≥y zN zN 0≮0  = x≥x zN
x≮y→x≥y zN (sN {n} Nn) 0≮Sn = ⊥-elim (true≢false (trans (sym (<-0S n)) 0≮Sn))
x≮y→x≥y (sN Nm) zN Sm≮n = x≥0 (sN Nm)
x≮y→x≥y (sN {m} Nm) (sN {n} Nn) Sm≮Sn =
  trans (<-SS n (succ₁ m)) (x≮y→x≥y Nm Nn (trans (sym (<-SS m n)) Sm≮Sn))

x>y→x≰y : ∀ {m n} → N m → N n → GT m n → NLE m n
x>y→x≰y zN          Nn          0>m   = ⊥-elim $ 0>x→⊥ Nn 0>m
x>y→x≰y (sN Nm)     zN          _     = Sx≰0 Nm
x>y→x≰y (sN {m} Nm) (sN {n} Nn) Sm>Sn =
  x≰y→Sx≰Sy m n (x>y→x≰y Nm Nn (trans (sym $ <-SS n m) Sm>Sn))

x>y∨x≤y : ∀ {m n} → N m → N n → GT m n ∨ LE m n
x>y∨x≤y zN          Nn          = inj₂ $ x≥0 Nn
x>y∨x≤y (sN {m} Nm) zN          = inj₁ $ <-0S m
x>y∨x≤y (sN {m} Nm) (sN {n} Nn) =
  [ (λ m>n → inj₁ (trans (<-SS n m) m>n))
  , (λ m≤n → inj₂ (x≤y→Sx≤Sy m≤n))
  ] (x>y∨x≤y Nm Nn)

x<y∨x≥y : ∀ {m n} → N m → N n → LT m n ∨ GE m n
x<y∨x≥y Nm Nn = x>y∨x≤y Nn Nm

x<y∨x≮y : ∀ {m n} → N m → N n → LT m n ∨ NLT m n
x<y∨x≮y Nm Nn = [ (λ m<n → inj₁ m<n)
                , (λ m≥n → inj₂ (x≥y→x≮y Nm Nn m≥n))
                ] (x<y∨x≥y Nm Nn)

x≤y∨x≰y : ∀ {m n} → N m → N n → LE m n ∨ NLE m n
x≤y∨x≰y zN Nn = inj₁ (0≤x Nn)
x≤y∨x≰y (sN Nm) zN = inj₂ (Sx≰0 Nm)
x≤y∨x≰y (sN {m} Nm) (sN {n} Nn) =
  [ (λ m≤n → inj₁ (x≤y→Sx≤Sy m≤n))
  , (λ m≰n → inj₂ (x≰y→Sx≰Sy m n m≰n))
  ] (x≤y∨x≰y Nm Nn)

x≡y→x≤y : ∀ {m n} → N m → N n → m ≡ n → LE m n
x≡y→x≤y {n = n} Nm Nn m≡n = subst (λ m' → LE m' n) (sym m≡n) (x≤x Nn)

x<y→x≤y : ∀ {m n} → N m → N n → LT m n → LE m n
x<y→x≤y Nm zN          m<0            = ⊥-elim $ x<0→⊥ Nm m<0
x<y→x≤y zN (sN {n} Nn) _              = <-0S $ succ₁ n
x<y→x≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn =
  x≤y→Sx≤Sy (x<y→x≤y Nm Nn (Sx<Sy→x<y Sm<Sn))

x<Sy→x≤y : ∀ {m n} → N m → N n → LT m (succ₁ n) → LE m n
x<Sy→x≤y zN Nn 0<Sn       = 0≤x Nn
x<Sy→x≤y (sN Nm) Nn Sm<Sn = Sm<Sn

x≤y→x<Sy : ∀ {m n} → N m → N n → LE m n → LT m (succ₁ n)
x≤y→x<Sy {n = n} zN      Nn 0≤n  = <-0S n
x≤y→x<Sy         (sN Nm) Nn Sm≤n = Sm≤n

x≤Sx : ∀ {m} → N m → LE m (succ₁ m)
x≤Sx Nm = x<y→x≤y Nm (sN Nm) (x<Sx Nm)

x<y→Sx≤y : ∀ {m n} → N m → N n → LT m n → LE (succ₁ m) n
x<y→Sx≤y Nm zN                   m<0   = ⊥-elim $ x<0→⊥ Nm m<0
x<y→Sx≤y zN          (sN {n} Nn) _     = x≤y→Sx≤Sy (0≤x Nn)
x<y→Sx≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn = trans (<-SS (succ₁ m) (succ₁ n)) Sm<Sn

Sx≤y→x<y : ∀ {m n} → N m → N n → LE (succ₁ m) n → LT m n
Sx≤y→x<y Nm          zN          Sm≤0   = ⊥-elim $ S≤0→⊥ Nm Sm≤0
Sx≤y→x<y zN          (sN {n} Nn) _      = <-0S n
Sx≤y→x<y (sN {m} Nm) (sN {n} Nn) SSm≤Sn =
  x<y→Sx<Sy (Sx≤y→x<y Nm Nn (Sx≤Sy→x≤y SSm≤Sn))

x≤y→x≯y : ∀ {m n} → N m → N n → LE m n → NGT m n
x≤y→x≯y zN          Nn          _    = 0≯x Nn
x≤y→x≯y (sN Nm)     zN          Sm≤0 = ⊥-elim $ S≤0→⊥ Nm Sm≤0
x≤y→x≯y (sN {m} Nm) (sN {n} Nn) Sm≤Sn =
  trans (<-SS n m) (x≤y→x≯y Nm Nn (trans (sym $ <-SS m (succ₁ n)) Sm≤Sn))

x≯y→x≤y : ∀ {m n} → N m → N n → NGT m n → LE m n
x≯y→x≤y zN Nn _ = 0≤x Nn
x≯y→x≤y (sN {m} Nm) zN Sm≯0 = ⊥-elim (true≢false (trans (sym (<-0S m)) Sm≯0))
x≯y→x≤y (sN {m} Nm) (sN {n} Nn) Sm≯Sn =
  trans (<-SS m (succ₁ n)) (x≯y→x≤y Nm Nn (trans (sym (<-SS n m)) Sm≯Sn))

Sx≯y→x≯y : ∀ {m n} → N m → N n → NGT (succ₁ m) n → NGT m n
Sx≯y→x≯y Nm Nn Sm≤n = x≤y→x≯y Nm Nn (Sx≤y→x≤y Nm Nn (x≯y→x≤y (sN Nm) Nn Sm≤n))

x>y∨x≯y : ∀ {m n} → N m → N n → GT m n ∨ NGT m n
x>y∨x≯y zN Nn                   = inj₂ (0≯x Nn)
x>y∨x≯y (sN {m} Nm) zN          = inj₁ (<-0S m)
x>y∨x≯y (sN {m} Nm) (sN {n} Nn) =
  [ (λ h → inj₁ (trans (<-SS n m) h))
  , (λ h → inj₂ (trans (<-SS n m) h))
  ] (x>y∨x≯y Nm Nn)

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
x≤x+y {n = n} (sN {m} Nm) Nn =
  succ₁ m < succ₁ (succ₁ m + n)
    ≡⟨ <-SS m (succ₁ m + n) ⟩
  m < succ₁ m + n
    ≡⟨ subst (λ t → m < succ₁ m + n ≡ m < t) (+-Sx m n) refl ⟩
  m < succ₁ (m + n)
    ≡⟨ refl ⟩
  m ≤ m + n
    ≡⟨ x≤x+y Nm Nn ⟩
  true ∎

x∸y<Sx : ∀ {m n} → N m → N n → LT (m ∸ n) (succ₁ m)
x∸y<Sx {m} Nm zN =
  m ∸ zero < succ₁ m
     ≡⟨ subst (λ t → m ∸ zero < succ₁ m ≡ t < succ₁ m) (∸-x0 m) refl ⟩
  m < succ₁ m
    ≡⟨ x<Sx Nm ⟩
  true ∎

x∸y<Sx zN (sN {n} Nn) =
  zero ∸ succ₁ n < succ₁ zero
    ≡⟨ subst (λ t → zero ∸ succ₁ n < succ₁ zero ≡ t < succ₁ zero)
             (∸-0S n)
             refl
    ⟩
  zero < succ₁ zero
    ≡⟨ <-0S zero ⟩
  true ∎

x∸y<Sx (sN {m} Nm) (sN {n} Nn) =
  succ₁ m ∸ succ₁ n < succ₁ (succ₁ m)
    ≡⟨ subst (λ t → succ₁ m ∸ succ₁ n < succ₁ (succ₁ m) ≡
                    t < succ₁ (succ₁ m))
             (∸-SS m n)
             refl
    ⟩
  m ∸ n < succ₁ (succ₁ m)
     ≡⟨ <-trans (∸-N Nm Nn) (sN Nm) (sN (sN Nm))
                (x∸y<Sx Nm Nn) (x<Sx (sN Nm))
     ⟩
  true ∎

Sx∸Sy<Sx : ∀ {m n} → N m → N n → LT (succ₁ m ∸ succ₁ n) (succ₁ m)
Sx∸Sy<Sx {m} {n} Nm Nn =
  succ₁ m ∸ succ₁ n < succ₁ m
    ≡⟨ subst (λ t → succ₁ m ∸ succ₁ n < succ₁ m ≡ t < succ₁ m)
             (∸-SS m n)
             refl
    ⟩
  m ∸ n < succ₁ m
     ≡⟨ x∸y<Sx Nm Nn ⟩
  true ∎

x>y→x∸y+y≡x : ∀ {m n} → N m → N n → GT m n → (m ∸ n) + n ≡ m
x>y→x∸y+y≡x zN          Nn 0>n  = ⊥-elim $ 0>x→⊥ Nn 0>n
x>y→x∸y+y≡x (sN {m} Nm) zN Sm>0 = trans (+-rightIdentity (∸-N (sN Nm) zN))
                                        (∸-x0 (succ₁ m))
x>y→x∸y+y≡x (sN {m} Nm) (sN {n} Nn) Sm>Sn =
  (succ₁ m ∸ succ₁ n) + succ₁ n
    ≡⟨ subst (λ t → (succ₁ m ∸ succ₁ n) + succ₁ n ≡ t + succ₁ n)
             (∸-SS m n)
             refl
    ⟩
  (m ∸ n) + succ₁ n
     ≡⟨ +-comm (∸-N Nm Nn) (sN Nn) ⟩
  succ₁ n + (m ∸ n)
    ≡⟨ +-Sx n (m ∸ n) ⟩
  succ₁ (n + (m ∸ n))
    ≡⟨ subst (λ t → succ₁ (n + (m ∸ n)) ≡ succ₁ t)
             (+-comm Nn (∸-N Nm Nn))
             refl
    ⟩
  succ₁ ((m ∸ n) + n)
    ≡⟨ subst (λ t → succ₁ ((m ∸ n) + n) ≡ succ₁ t)
             (x>y→x∸y+y≡x Nm Nn (trans (sym $ <-SS n m) Sm>Sn))
             refl
    ⟩
  succ₁ m ∎

x≤y→y∸x+x≡y : ∀ {m n} → N m → N n → LE m n → (n ∸ m) + m ≡ n
x≤y→y∸x+x≡y {n = n} zN      Nn 0≤n  = trans (+-rightIdentity (∸-N Nn zN))
                                            (∸-x0 n)
x≤y→y∸x+x≡y         (sN Nm) zN Sm≤0 = ⊥-elim $ S≤0→⊥ Nm Sm≤0
x≤y→y∸x+x≡y (sN {m} Nm) (sN {n} Nn) Sm≤Sn =
  (succ₁ n ∸ succ₁ m) + succ₁ m
    ≡⟨ subst (λ t → (succ₁ n ∸ succ₁ m) + succ₁ m ≡ t + succ₁ m)
             (∸-SS n m)
             refl
    ⟩
  (n ∸ m) + succ₁ m
     ≡⟨ +-comm (∸-N Nn Nm) (sN Nm) ⟩
  succ₁ m + (n ∸ m)
    ≡⟨ +-Sx m (n ∸ m) ⟩
  succ₁ (m + (n ∸ m))
    ≡⟨ subst (λ t → succ₁ (m + (n ∸ m)) ≡ succ₁ t)
             (+-comm Nm (∸-N Nn Nm))
             refl
    ⟩
  succ₁ ((n ∸ m) + m)
    ≡⟨ subst (λ t → succ₁ ((n ∸ m) + m) ≡ succ₁ t)
             (x≤y→y∸x+x≡y Nm Nn (trans (sym $ <-SS m (succ₁ n)) Sm≤Sn))
             refl
    ⟩
  succ₁ n ∎

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

x<y→y≡z→x<z : ∀ {m n o} → LT m n → n ≡ o → LT m o
x<y→y≡z→x<z {m} m<n n≡o = subst (λ n' → LT m n') n≡o m<n

x≡y→y<z→x<z : ∀ {m n o} → m ≡ n → LT n o → LT m o
x≡y→y<z→x<z {o = o} m≡n n<o = subst (λ m' → LT m' o) (sym m≡n) n<o

x≥y→y>0→x∸y<x : ∀ {m n} → N m → N n → GE m n → GT n zero → LT (m ∸ n) m
x≥y→y>0→x∸y<x Nm          zN          _     0>0  = ⊥-elim $ x>x→⊥ zN 0>0
x≥y→y>0→x∸y<x zN          (sN Nn)     0≥Sn  _    = ⊥-elim $ S≤0→⊥ Nn 0≥Sn
x≥y→y>0→x∸y<x (sN {m} Nm) (sN {n} Nn) Sm≥Sn Sn>0 =
  (succ₁ m ∸ succ₁ n) < (succ₁ m)
    ≡⟨ subst (λ t → (succ₁ m ∸ succ₁ n) < (succ₁ m) ≡ t < (succ₁ m))
             (∸-SS m n)
             refl
    ⟩
  (m ∸ n) < (succ₁ m)
     ≡⟨ x∸y<Sx Nm Nn ⟩
  true ∎

x<y→y≤z→x<z : ∀ {m n o} → N m → N n → N o → LT m n → LE n o → LT m o
x<y→y≤z→x<z Nm Nn No m<n n≤o =
  [ (λ n<o → <-trans Nm Nn No m<n n<o)
  , (λ n≡o → x<y→y≡z→x<z m<n n≡o)
  ] (x<Sy→x<y∨x≡y Nn No n≤o)

------------------------------------------------------------------------------
-- Properties about the lexicographical order

xy<00→⊥ : ∀ {m n} → N m → N n → ¬ (Lexi m n zero zero)
xy<00→⊥ Nm Nn mn<00 =
  [ (λ m<0     → ⊥-elim $ x<0→⊥ Nm m<0)
  , (λ m≡0∧n<0 → ⊥-elim $ x<0→⊥ Nn (∧-proj₂ m≡0∧n<0))
  ]
  mn<00

0Sx<00→⊥ : ∀ {m} → ¬ (Lexi zero (succ₁ m) zero zero)
0Sx<00→⊥ 0Sm<00 =
  [ 0<0→⊥
  , (λ 0≡0∧Sm<0 → S<0→⊥ (∧-proj₂ 0≡0∧Sm<0))
  ]
  0Sm<00

Sxy₁<0y₂→⊥ : ∀ {m n₁ n₂} → ¬ (Lexi (succ₁ m) n₁ zero n₂)
Sxy₁<0y₂→⊥ Smn₁<0n₂ =
  [ S<0→⊥
  , (λ Sm≡0∧n₁<n₂ → ⊥-elim $ 0≢S $ sym $ ∧-proj₁ Sm≡0∧n₁<n₂)
  ]
  Smn₁<0n₂

x₁y<x₂0→x₁<x₂ : ∀ {m₁ n} → N n → ∀ {m₂} → Lexi m₁ n m₂ zero → LT m₁ m₂
x₁y<x₂0→x₁<x₂ Nn m₁n<m₂0 =
  [ (λ m₁<n₁     → m₁<n₁)
  , (λ m₁≡n₁∧n<0 → ⊥-elim $ x<0→⊥ Nn (∧-proj₂ m₁≡n₁∧n<0))
  ]
  m₁n<m₂0

xy₁<0y₂→x≡0∧y₁<y₂ : ∀ {m} → N m → ∀ {n₁ n₂} → Lexi m n₁ zero n₂ →
                    m ≡ zero ∧ LT n₁ n₂
xy₁<0y₂→x≡0∧y₁<y₂ Nm mn₁<0n₂ =
  [ (λ m<0       → ⊥-elim $ x<0→⊥ Nm m<0)
  , (λ m≡0∧n₁<n₂ → m≡0∧n₁<n₂)
  ]
  mn₁<0n₂

[Sx∸Sy,Sy]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     Lexi (succ₁ m ∸ succ₁ n) (succ₁ n) (succ₁ m) (succ₁ n)
[Sx∸Sy,Sy]<[Sx,Sy] Nm Nn = inj₁ (Sx∸Sy<Sx Nm Nn)

[Sx,Sy∸Sx]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     Lexi (succ₁ m) (succ₁ n ∸ succ₁ m) (succ₁ m) (succ₁ n)
[Sx,Sy∸Sx]<[Sx,Sy] Nm Nn = inj₂ (refl , Sx∸Sy<Sx Nn Nm)
