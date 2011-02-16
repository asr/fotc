------------------------------------------------------------------------------
-- Properties of the inequalities
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Inequalities.PropertiesI where

open import LTC.Base
open import LTC.Base.Properties using ( x≡y→Sx≡Sy )

open import Common.Function using ( _$_ )

open import LTC.Relation.Binary.EqReasoning

open import LTC-PCF.Data.Nat
  using ( _+_ ; _∸_
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.Data.Nat.Inequalities
   using ( _<_ ; _≤_
         ; GE ; GT ; LE ; LT ; NGT ; NLE ; NLT
         ; LT₂
         )
open import LTC-PCF.Data.Nat.Inequalities.EquationsI public
  using ( <-00 ; <-S0 ; <-0S ; <-SS )
open import LTC-PCF.Data.Nat.PropertiesI
  using ( +-N ; ∸-N
        ; +-Sx
        ; +-comm
        ; +-rightIdentity
        ; ∸-0S ; ∸-SS ; ∸-x0
        )

------------------------------------------------------------------------------
-- Elimination properties
-- (See LTC.Data.Nat.Inequalities.Properties)

0<0→⊥ : ¬ LT zero zero
0<0→⊥ 0<0 = true≠false $ trans (sym 0<0) <-00

S<0→⊥ : {d : D} → ¬ LT (succ d) zero
S<0→⊥ {d} Sd<0 = true≠false $ trans (sym Sd<0) (<-S0 d)

x<0→⊥ : ∀ {n} → N n → ¬ (LT n zero)
x<0→⊥ zN     0<0  = 0<0→⊥ 0<0
x<0→⊥ (sN _) Sn<0 = S<0→⊥ Sn<0

x<x→⊥ : ∀ {n} → N n → ¬ (LT n n)
x<x→⊥ zN          0<0   = 0<0→⊥ 0<0
x<x→⊥ (sN {n} Nn) Sn<Sn = ⊥-elim $ x<x→⊥ Nn (trans (sym $ <-SS n n) Sn<Sn)

0>0→⊥ : ¬ GT zero zero
0>0→⊥ 0>0 = true≠false $ trans (sym 0>0) <-00

0>S→⊥ : {d : D} → ¬ GT zero (succ d)
0>S→⊥ {d} 0>Sd = true≠false (trans (sym 0>Sd) (<-S0 d))

0>x→⊥ : ∀ {n} → N n → ¬ (GT zero n)
0>x→⊥ zN     0>0  = 0>0→⊥ 0>0
0>x→⊥ (sN _) 0>Sn = 0>S→⊥ 0>Sn

x>x→⊥ : ∀ {n} → N n → ¬ (GT n n)
x>x→⊥ Nn = x<x→⊥ Nn

S≤0→⊥ : ∀ {n} → N n → ¬ (LE (succ n) zero)
S≤0→⊥ zN         S0≤0  = true≠false (trans (sym S0≤0)
                                           (trans (<-SS zero zero) <-00))
S≤0→⊥ (sN {n} _) SSn≤0 = true≠false (trans (sym SSn≤0)
                                           (trans (<-SS (succ n) zero) (<-S0 n)))

0≥S→⊥ : ∀ {n} → N n → ¬ (GE zero (succ n))
0≥S→⊥ Nn 0≥Sn = S≤0→⊥ Nn 0≥Sn

x<y→y<x→⊥ : ∀ {m n} → N m → N n → LT m n → ¬ (LT n m)
x<y→y<x→⊥ zN      Nn              0<n   n<0   = ⊥-elim (0>x→⊥ Nn n<0)
x<y→y<x→⊥ (sN Nm) zN              Sm<0  0<Sm  = ⊥-elim (0>x→⊥ (sN Nm) Sm<0)
x<y→y<x→⊥ (sN {m} Nm) (sN {n} Nn) Sm<Sn Sn<Sm =
  x<y→y<x→⊥ Nm Nn (trans (sym (<-SS m n)) Sm<Sn) (trans (sym (<-SS n m)) Sn<Sm)

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

x<y→Sx<Sy : ∀ {m n} → LT m n → LT (succ m) (succ n)
x<y→Sx<Sy {m} {n} m<n = trans (<-SS m n) m<n

Sx<Sy→x<y : ∀ {m n} → LT (succ m) (succ n) → LT m n
Sx<Sy→x<y {m} {n} Sm<Sn = trans (sym $ <-SS m n) Sm<Sn

x≤x : ∀ {n} → N n → LE n n
x≤x zN          = <-0S zero
x≤x (sN {n} Nn) = trans (<-SS n (succ n)) (x≤x Nn)

x≤y→Sx≤Sy : ∀ {m n} → LE m n → LE (succ m) (succ n)
x≤y→Sx≤Sy {m} {n} m≤n = trans (<-SS m (succ n)) m≤n

Sx≤Sy→x≤y : ∀ {m n} → LE (succ m) (succ n) → LE m n
Sx≤Sy→x≤y {m} {n} Sm≤Sn = trans (sym $ <-SS m (succ n)) Sm≤Sn

x≥y→x≮y : ∀ {m n} → N m → N n → GE m n → NLT m n
x≥y→x≮y zN          zN          _     = x≰x zN
x≥y→x≮y zN          (sN Nn)     0≥Sn  = ⊥-elim $ 0≥S→⊥ Nn 0≥Sn
x≥y→x≮y (sN {m} Nm) zN          _     = <-S0 m
x≥y→x≮y (sN {m} Nm) (sN {n} Nn) Sm≥Sn =
  trans (<-SS m n) (x≥y→x≮y Nm Nn (trans (sym $ <-SS n (succ m)) Sm≥Sn))

x≤y→x≯y : ∀ {m n} → N m → N n → LE m n → NGT m n
x≤y→x≯y zN          Nn          _    = 0≯x Nn
x≤y→x≯y (sN Nm)     zN          Sm≤0 = ⊥-elim $ S≤0→⊥ Nm Sm≤0
x≤y→x≯y (sN {m} Nm) (sN {n} Nn) Sm≤Sn =
  trans (<-SS n m) (x≤y→x≯y Nm Nn (trans (sym $ <-SS m (succ n)) Sm≤Sn))

x>y∨x≤y : ∀ {m n} → N m → N n → GT m n ∨ LE m n
x>y∨x≤y zN          Nn          = inj₂ $ x≥0 Nn
x>y∨x≤y (sN {m} Nm) zN          = inj₁ $ <-0S m
x>y∨x≤y (sN {m} Nm) (sN {n} Nn) =
  [ (λ m>n → inj₁ (trans (<-SS n m) m>n))
  , (λ m≤n → inj₂ (trans (<-SS m (succ n)) m≤n))
  ] (x>y∨x≤y Nm Nn)

x<y∨x≥y : ∀ {m n} → N m → N n → LT m n ∨ GE m n
x<y∨x≥y Nm Nn = x>y∨x≤y Nn Nm

x≡y→x≤y : ∀ {m n} {Nm : N m} {Nn : N n} → m ≡ n → LE m n
x≡y→x≤y {Nm = Nm} refl = x≤x Nm

x<y→x≤y : ∀ {m n} → N m → N n → LT m n → LE m n
x<y→x≤y Nm zN          m<0            = ⊥-elim $ x<0→⊥ Nm m<0
x<y→x≤y zN (sN {n} Nn) _              = <-0S $ succ n
x<y→x≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn =
  x≤y→Sx≤Sy (x<y→x≤y Nm Nn (Sx<Sy→x<y Sm<Sn))

x≤Sx : ∀ {m} → N m → LE m (succ m)
x≤Sx Nm = x<y→x≤y Nm (sN Nm) (x<Sx Nm)

x<y→Sx≤y : ∀ {m n} → N m → N n → LT m n → LE (succ m) n
x<y→Sx≤y Nm zN               m<0       = ⊥-elim $ x<0→⊥ Nm m<0
x<y→Sx≤y zN          (sN {n} Nn) _     = x≤y→Sx≤Sy (0≤x Nn)
x<y→Sx≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn = trans (<-SS (succ m) (succ n)) Sm<Sn

Sx≤y→x<y : ∀ {m n} → N m → N n → LE (succ m) n → LT m n
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
x≤x+y {n = n} (sN {m} Nm) Nn =
  begin
    (succ m) < (succ (succ m + n)) ≡⟨ <-SS m (succ m + n) ⟩
    m < (succ m + n)               ≡⟨ subst (λ t → m < (succ m + n) ≡ m < t)
                                             (+-Sx m n)
                                             refl
                                    ⟩
    m < (succ (m + n))             ≡⟨ refl ⟩
    m ≤ (m + n)                    ≡⟨ x≤x+y Nm Nn ⟩
    true
  ∎

x∸y<Sx : ∀ {m n} → N m → N n → LT (m ∸ n) (succ m)
x∸y<Sx {m} Nm zN =
  begin
    (m ∸ zero) < (succ m) ≡⟨ subst (λ t → (m ∸ zero) < (succ m) ≡
                                          t  < (succ m))
                                    (∸-x0 m)
                                    refl
                           ⟩
    m < (succ m)          ≡⟨ x<Sx Nm ⟩
    true
  ∎

x∸y<Sx zN (sN {n} Nn) =
  begin
    (zero ∸ succ n) < (succ zero)
      ≡⟨ subst (λ t → (zero ∸ succ n) < (succ zero) ≡ t < (succ zero))
               (∸-0S Nn)
               refl
      ⟩
    zero < succ zero ≡⟨ <-0S zero ⟩
    true
  ∎

x∸y<Sx (sN {m} Nm) (sN {n} Nn) =
  begin
    (succ m ∸ succ n) < (succ (succ m))
      ≡⟨ subst (λ t → (succ m ∸ succ n) < (succ (succ m)) ≡
                      t < (succ (succ m)))
               (∸-SS Nm Nn)
               refl
      ⟩
    (m ∸ n) < (succ (succ m))
      ≡⟨ <-trans (∸-N Nm Nn) (sN Nm) (sN (sN Nm))
                 (x∸y<Sx Nm Nn) (x<Sx (sN Nm))
      ⟩
    true
  ∎

Sx∸Sy<Sx : ∀ {m n} → N m → N n → LT (succ m ∸ succ n) (succ m)
Sx∸Sy<Sx {m} {n} Nm Nn =
  begin
    (succ m ∸ succ n) < (succ m) ≡⟨ subst (λ t → (succ m ∸ succ n) <
                                                     (succ m) ≡
                                                  t < (succ m))
                                           (∸-SS Nm Nn)
                                           refl
                                  ⟩
    (m ∸ n) < (succ m)           ≡⟨ x∸y<Sx Nm Nn ⟩
    true
    ∎

x>y→x∸y+y≡x : ∀ {m n} → N m → N n → GT m n → (m ∸ n) + n ≡ m
x>y→x∸y+y≡x zN          Nn 0>n  = ⊥-elim $ 0>x→⊥ Nn 0>n
x>y→x∸y+y≡x (sN {m} Nm) zN Sm>0 = trans (+-rightIdentity (∸-N (sN Nm) zN))
                                        (∸-x0 (succ m))
x>y→x∸y+y≡x (sN {m} Nm) (sN {n} Nn) Sm>Sn =
  begin
    (succ m ∸ succ n) + succ n ≡⟨ subst (λ t → (succ m ∸ succ n) + succ n ≡
                                               t + succ n)
                                        (∸-SS Nm Nn)
                                        refl
                               ⟩
    (m ∸ n) + succ n           ≡⟨ +-comm (∸-N Nm Nn) (sN Nn) ⟩
    succ n + (m ∸ n)           ≡⟨ +-Sx n (m ∸ n) ⟩
    succ (n + (m ∸ n))         ≡⟨ subst (λ t → succ (n + (m ∸ n)) ≡ succ t)
                                        (+-comm Nn (∸-N Nm Nn))
                                        refl
                               ⟩
    succ ((m ∸ n) + n)         ≡⟨ subst (λ t → succ ((m ∸ n) + n) ≡ succ t)
                                        (x>y→x∸y+y≡x Nm Nn
                                             (trans (sym $ <-SS n m) Sm>Sn))
                                        refl
                               ⟩
    succ m
  ∎

x≤y→y∸x+x≡y : ∀ {m n} → N m → N n → LE m n → (n ∸ m) + m ≡ n
x≤y→y∸x+x≡y {n = n} zN      Nn 0≤n  = trans (+-rightIdentity (∸-N Nn zN))
                                            (∸-x0 n)
x≤y→y∸x+x≡y         (sN Nm) zN Sm≤0 = ⊥-elim $ S≤0→⊥ Nm Sm≤0
x≤y→y∸x+x≡y (sN {m} Nm) (sN {n} Nn) Sm≤Sn =
  begin
    (succ n ∸ succ m) + succ m ≡⟨ subst (λ t → (succ n ∸ succ m) + succ m ≡
                                               t + succ m)
                                        (∸-SS Nn Nm)
                                        refl
                               ⟩
    (n ∸ m) + succ m           ≡⟨ +-comm (∸-N Nn Nm) (sN Nm) ⟩
    succ m + (n ∸ m)           ≡⟨ +-Sx m (n ∸ m) ⟩
    succ (m + (n ∸ m))         ≡⟨ subst (λ t → succ (m + (n ∸ m)) ≡ succ t)
                                        (+-comm Nm (∸-N Nn Nm))
                                        refl
                               ⟩
    succ ((n ∸ m) + m)         ≡⟨ subst (λ t → succ ((n ∸ m) + m) ≡ succ t)
                                        (x≤y→y∸x+x≡y Nm Nn
                                             (trans (sym $ <-SS m (succ n))
                                                    Sm≤Sn))
                                        refl
                               ⟩
    succ n
  ∎

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
  , (λ m≡n → inj₂ (x≡y→Sx≡Sy m≡n))
  ]
  m<n∨m≡n

  where
    m<n∨m≡n : LT m n ∨ m ≡ n
    m<n∨m≡n = x<Sy→x<y∨x≡y Nm Nn (trans (sym $ <-SS m (succ n)) Sm<SSn)

x<y→y≡z→x<z : ∀ {m n o} → LT m n → n ≡ o → LT m o
x<y→y≡z→x<z m<n refl = m<n

x≡y→y<z→x<z : ∀ {m n o} → m ≡ n → LT n o → LT m o
x≡y→y<z→x<z refl n<o = n<o

x≥y→y>0→x-y<x : ∀ {m n} → N m → N n → GE m n → GT n zero → LT (m ∸ n) m
x≥y→y>0→x-y<x Nm          zN          _     0>0  = ⊥-elim $ x>x→⊥ zN 0>0
x≥y→y>0→x-y<x zN          (sN Nn)     0≥Sn  _    = ⊥-elim $ S≤0→⊥ Nn 0≥Sn
x≥y→y>0→x-y<x (sN {m} Nm) (sN {n} Nn) Sm≥Sn Sn>0 =
  begin
    (succ m ∸ succ n) < (succ m)
      ≡⟨ subst (λ t → (succ m ∸ succ n) < (succ m) ≡ t < (succ m))
               (∸-SS Nm Nn)
               refl
      ⟩
    (m ∸ n) < (succ m) ≡⟨ x∸y<Sx Nm Nn ⟩
    true
  ∎

------------------------------------------------------------------------------
-- Properties about LT₂

xy<00→⊥ : ∀ {m n} → N m → N n → ¬ (LT₂ m n zero zero)
xy<00→⊥ Nm Nn mn<00 =
  [ (λ m<0     → ⊥-elim $ x<0→⊥ Nm m<0)
  , (λ m≡0∧n<0 → ⊥-elim $ x<0→⊥ Nn (∧-proj₂ m≡0∧n<0))
  ]
  mn<00

0Sx<00→⊥ : ∀ {m} → N m → ¬ (LT₂ zero (succ m) zero zero)
0Sx<00→⊥ Nm 0Sm<00 =
  [ 0<0→⊥
  , (λ 0≡0∧Sm<0 → S<0→⊥ (∧-proj₂ 0≡0∧Sm<0))
  ]
  0Sm<00

Sxy₁<0y₂→⊥ : ∀ {m n₁ n₂} → N m → N n₁ → N n₂ → ¬ (LT₂ (succ m) n₁ zero n₂)
Sxy₁<0y₂→⊥ Nm Nn₁ Nn₂ Smn₁<0n₂ =
  [ S<0→⊥
  , (λ Sm≡0∧n₁<n₂ → ⊥-elim $ 0≠S $ sym $ ∧-proj₁ Sm≡0∧n₁<n₂)
  ]
  Smn₁<0n₂

x₁y<x₂0→x₁<x₂ : ∀ {m₁ n m₂} → N m₁ → N n → N m₂ → LT₂ m₁ n m₂ zero → LT m₁ m₂
x₁y<x₂0→x₁<x₂ Nm₁ Nn Nm₂ m₁n<m₂zero =
  [ (λ m₁<n₁     → m₁<n₁)
  , (λ m₁≡n₁∧n<0 → ⊥-elim $ x<0→⊥ Nn (∧-proj₂ m₁≡n₁∧n<0))
  ]
  m₁n<m₂zero

xy₁<0y₂→x≡0∧y₁<y₂ : ∀ {m n₁ n₂} → N m → N n₁ → N n₂ → LT₂ m n₁ zero n₂ →
                    m ≡ zero ∧ LT n₁ n₂
xy₁<0y₂→x≡0∧y₁<y₂ Nm Nn₁ Nn₂ mn₁<0n₂ =
  [ (λ m<0          → ⊥-elim $ x<0→⊥ Nm m<0)
  , (λ m≡zero∧n₁<n₂ → m≡zero∧n₁<n₂)
  ]
  mn₁<0n₂

[Sx∸Sy,Sy]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     LT₂ (succ m ∸ succ n) (succ n) (succ m) (succ n)
[Sx∸Sy,Sy]<[Sx,Sy] {m} {n} Nm Nn = inj₁ (Sx∸Sy<Sx Nm Nn)

[Sx,Sy∸Sx]<[Sx,Sy] : ∀ {m n} → N m → N n →
                     LT₂ (succ m) (succ n ∸ succ m) (succ m) (succ n)
[Sx,Sy∸Sx]<[Sx,Sy] {m} {n} Nm Nn = inj₂ (refl , Sx∸Sy<Sx Nn Nm)
