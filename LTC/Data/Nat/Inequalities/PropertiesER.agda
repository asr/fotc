------------------------------------------------------------------------------
-- Properties of the inequalities (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Data.Nat.Inequalities.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.PropertiesER
open import LTC.Relation.Equalities.PropertiesER

open import MyStdLib.Data.Sum
open import MyStdLib.Function
import MyStdLib.Relation.Binary.EqReasoning
open module IPER = MyStdLib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

------------------------------------------------------------------------------

x≥0 : {n : D} → N n → GE n zero
x≥0 zN          = lt-00
x≥0 (sN {n} Nn) = lt-S0 n

0≤x : {n : D} → N n → LE zero n
0≤x Nn = x≥0 Nn

¬x<0 : {n : D} → N n → ¬ (LT n zero)
¬x<0 zN 0<0           = true≠false (trans (sym 0<0) (lt-00))
¬x<0 (sN {n} Nn) Sn<0 = true≠false (trans (sym Sn<0) (lt-S0 n))

¬0>x : {n : D} → N n → ¬ (GT zero n)
¬0>x Nn 0>n = true≠false $ trans (sym 0>n ) $ x≥0 Nn

¬S≤0 : {d : D} → ¬ (LE (succ d) zero)
¬S≤0 {d} Sd≤0 = true≠false $ trans (sym $ lt-0S d ) Sd≤0

x<Sx : {n : D} → N n → LT n (succ n)
x<Sx zN          = lt-0S zero
x<Sx (sN {n} Nn) = trans (lt-SS n (succ n)) (x<Sx Nn)

x>y∨x≤y : {m n : D} → N m → N n → GT m n ∨ LE m n
x>y∨x≤y zN          Nn          = inj₂ $ x≥0 Nn
x>y∨x≤y (sN {m} Nm) zN          = inj₁ $ lt-0S m
x>y∨x≤y (sN {m} Nm) (sN {n} Nn) =
  subst (λ a → a ≡ true ∨ a ≡ false)
        (sym $ lt-SS n m)
        (x>y∨x≤y Nm Nn )

x<y∨x≥y : {m n : D} → N m → N n → LT m n ∨ GE m n
x<y∨x≥y Nm Nn = x>y∨x≤y Nn Nm

¬x<x : {m : D} → N m → ¬ (LT m m)
¬x<x zN          0<0   = ⊥-elim (true≠false (trans (sym 0<0) lt-00))
¬x<x (sN {m} Nm) Sm<Sm = ⊥-elim (¬x<x Nm (trans (sym (lt-SS m m)) Sm<Sm))

¬x>x : {m : D} → N m → ¬ (GT m m)
¬x>x Nm = ¬x<x Nm

x≤x : {m : D} → N m → LE m m
x≤x zN          = lt-00
x≤x (sN {m} Nm) = trans (lt-SS m m) (x≤x Nm)

-- TODO: Why not a dot pattern?
x≡y→x≤y : {m n : D} → N m → N n → m ≡ n → LE m n
x≡y→x≤y Nm Nn refl = x≤x Nm

x<y→x≤y : {m n : D} → N m → N n → LT m n → LE m n
x<y→x≤y Nm zN          m<0            = ⊥-elim (¬x<0 Nm m<0)
x<y→x≤y zN (sN {n} Nn) _              = lt-S0 n
x<y→x≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn =
  begin
    lt (succ n) (succ m) ≡⟨ lt-SS n m ⟩
    lt n m ≡⟨ x<y→x≤y Nm Nn (trans (sym (lt-SS m n)) Sm<Sn) ⟩
    false
  ∎

x<y→Sx≤y : {m n : D} → N m → N n → LT m n → LE (succ m) n
x<y→Sx≤y Nm zN               m<0       = ⊥-elim (¬x<0 Nm m<0)
x<y→Sx≤y zN (sN zN)          _         = trans (lt-SS zero zero) lt-00
x<y→Sx≤y zN (sN (sN {n} Nn)) _         = trans (lt-SS (succ n) zero) (lt-S0 n)
x<y→Sx≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn =
  trans (lt-SS n (succ m)) (x<y→Sx≤y Nm Nn (trans (sym (lt-SS m n)) Sm<Sn))

Sx≤y→x<y : {m n : D} → N m → N n → LE (succ m) n → LT m n
Sx≤y→x<y Nm          zN          Sm≤0   = ⊥-elim (¬S≤0 Sm≤0)
Sx≤y→x<y zN          (sN {n} Nn) _      = lt-0S n
Sx≤y→x<y (sN {m} Nm) (sN {n} Nn) SSm≤Sn =
  trans (lt-SS m n) (Sx≤y→x<y Nm Nn (trans (sym (lt-SS n (succ m))) SSm≤Sn))

<-trans : {m n o : D} → N m → N n → N o → LT m n → LT n o → LT m o
<-trans zN          zN           _          0<0   _    = ⊥-elim (¬x<0 zN 0<0)
<-trans zN          (sN Nn)     zN          _     Sn<0 = ⊥-elim (¬x<0 (sN Nn) Sn<0)
<-trans zN          (sN Nn)     (sN {o} No) _     _    = lt-0S o
<-trans (sN Nm)     Nn          zN          _     n<0  = ⊥-elim (¬x<0 Nn n<0)
<-trans (sN Nm)     zN          (sN No)     Sm<0  _    = ⊥-elim (¬x<0 (sN Nm) Sm<0)
<-trans (sN {m} Nm) (sN {n} Nn) (sN {o} No) Sm<Sn Sn<So =
  begin
    lt (succ m) (succ o) ≡⟨ lt-SS m o ⟩
    lt m o ≡⟨ <-trans Nm Nn No
                       (trans (sym (lt-SS m n)) Sm<Sn)
                       (trans (sym (lt-SS n o)) Sn<So) ⟩
    true
  ∎

≤-trans : {m n o : D} → N m → N n → N o → LE m n → LE n o → LE m o
≤-trans zN      Nn              No          _     _     = 0≤x No
≤-trans (sN Nm) zN              No          Sm≤0  _     = ⊥-elim (¬S≤0 Sm≤0)
≤-trans (sN Nm) (sN Nn)         zN          _     Sn≤0  = ⊥-elim (¬S≤0 Sn≤0)
≤-trans (sN {m} Nm) (sN {n} Nn) (sN {o} No) Sm≤Sn Sn≤So =
  trans (lt-SS o m)
        (≤-trans Nm Nn No
                 (trans (sym (lt-SS n m)) Sm≤Sn)
                 (trans (sym (lt-SS o n)) Sn≤So))

Sx≤Sy→x≤y : {m n : D} → LE (succ m) (succ n) → LE m n
Sx≤Sy→x≤y {m} {n} Sm≤Sn = trans (sym (lt-SS n m)) Sm≤Sn

x≤x+y : {m n : D} → N m → N n → LE m (m + n)
x≤x+y         zN          Nn = x≥0 (+-N zN Nn)
x≤x+y {n = n} (sN {m} Nm) Nn =
  begin
    lt (succ m + n) (succ m)   ≡⟨ subst (λ t → lt (succ m + n) (succ m) ≡
                                               lt t (succ m))
                                        (+-Sx m n)
                                        refl
                               ⟩
    lt (succ (m + n)) (succ m) ≡⟨ lt-SS (m + n) m ⟩
    lt (m + n) m               ≡⟨ x≤x+y Nm Nn ⟩
    false
  ∎

x-y<Sx : {m n : D} → N m → N n → LT (m - n) (succ m)
x-y<Sx {m} Nm zN =
  begin
    lt (m - zero) (succ m) ≡⟨ subst (λ t → lt (m - zero) (succ m) ≡
                                           lt t (succ m))
                                    (minus-x0 m)
                                    refl
                           ⟩
    lt m (succ m)          ≡⟨ x<Sx Nm ⟩
    true
  ∎

x-y<Sx zN (sN {n} Nn) =
  begin
    lt (zero - succ n) (succ zero)
      ≡⟨ subst (λ t → lt (zero - succ n) (succ zero) ≡ lt t (succ zero))
               (minus-0S n)
               refl
      ⟩
    lt zero (succ zero) ≡⟨ lt-0S zero ⟩
    true
  ∎

x-y<Sx (sN {m} Nm) (sN {n} Nn) =
  begin
    lt (succ m - succ n) (succ (succ m))
      ≡⟨ subst (λ t → lt (succ m - succ n) (succ (succ m)) ≡
                      lt t (succ (succ m)))
               (minus-SS m n)
               refl
      ⟩
    lt (m - n) (succ (succ m))
      ≡⟨ <-trans (minus-N Nm Nn) (sN Nm) (sN (sN Nm))
                 (x-y<Sx Nm Nn) (x<Sx (sN Nm))
      ⟩
    true
  ∎

Sx-Sy<Sx : {m n : D} → N m → N n → LT (succ m - succ n) (succ m)
Sx-Sy<Sx {m} {n} Nm Nn =
  begin
    lt (succ m - succ n) (succ m) ≡⟨ subst (λ t → lt (succ m - succ n)
                                                     (succ m) ≡
                                                  lt t (succ m))
                                           (minus-SS m n)
                                           refl
                                  ⟩
    lt (m - n) (succ m)           ≡⟨ x-y<Sx Nm Nn ⟩
    true
    ∎

x>y→x-y+y≡x : {m n : D} → N m → N n → GT m n → (m - n) + n ≡ m
x>y→x-y+y≡x zN          Nn 0>n  = ⊥-elim (¬0>x Nn 0>n)
x>y→x-y+y≡x (sN {m} Nm) zN Sm>0 = trans (+-rightIdentity (minus-N (sN Nm) zN))
                                        (minus-x0 (succ m))
x>y→x-y+y≡x (sN {m} Nm) (sN {n} Nn) Sm>Sn =
  begin
    (succ m - succ n) + succ n ≡⟨ subst (λ t → (succ m - succ n) + succ n ≡
                                               t + succ n)
                                        (minus-SS m n)
                                        refl
                               ⟩
    (m - n) + succ n           ≡⟨ +-comm (minus-N Nm Nn) (sN Nn) ⟩
    succ n + (m - n)           ≡⟨ +-Sx n (m - n) ⟩
    succ (n + (m - n))         ≡⟨ subst (λ t → succ (n + (m - n)) ≡ succ t )
                                        (+-comm Nn (minus-N Nm Nn))
                                        refl
                               ⟩
    succ ((m - n) + n)         ≡⟨ subst (λ t → succ ((m - n) + n) ≡ succ t )
                                        (x>y→x-y+y≡x Nm Nn
                                             (trans (sym (lt-SS n m)) Sm>Sn) )
                                        refl
                               ⟩
    succ m
  ∎

x≤y→y-x+x≡y : {m n : D} → N m → N n → LE m n → (n - m) + m ≡ n
x≤y→y-x+x≡y {n = n} zN      Nn 0≤n  = trans (+-rightIdentity (minus-N Nn zN))
                                            (minus-x0 n)
x≤y→y-x+x≡y         (sN Nm) zN Sm≤0 = ⊥-elim (¬S≤0 Sm≤0)
x≤y→y-x+x≡y (sN {m} Nm) (sN {n} Nn) Sm≤Sn =
  begin
    (succ n - succ m) + succ m ≡⟨ subst (λ t → (succ n - succ m) + succ m ≡
                                               t + succ m)
                                        (minus-SS n m)
                                        refl
                               ⟩
    (n - m) + succ m           ≡⟨ +-comm (minus-N Nn Nm) (sN Nm) ⟩
    succ m + (n - m)           ≡⟨ +-Sx m (n - m) ⟩
    succ (m + (n - m))         ≡⟨ subst (λ t → succ (m + (n - m)) ≡ succ t )
                                        (+-comm Nm (minus-N Nn Nm))
                                        refl
                               ⟩
    succ ((n - m) + m)         ≡⟨ subst (λ t → succ ((n - m) + m) ≡ succ t )
                                        (x≤y→y-x+x≡y Nm Nn
                                             (trans (sym (lt-SS n m)) Sm≤Sn) )
                                        refl
                               ⟩
    succ n
  ∎

x<y→x<Sy : {m n : D} → N m → N n → LT m n → LT m (succ n)
x<y→x<Sy Nm          zN          m<0   = ⊥-elim (¬x<0 Nm m<0)
x<y→x<Sy zN          (sN {n} Nn) 0<Sn  = lt-0S (succ n)
x<y→x<Sy (sN {m} Nm) (sN {n} Nn) Sm<Sn =
  trans (lt-SS m (succ n)) (x<y→x<Sy Nm Nn (trans (sym (lt-SS m n)) Sm<Sn))

x<Sy→x<y∨x≡y : {m n : D} → N m → N n → LT m (succ n) → LT m n ∨ m ≡ n
x<Sy→x<y∨x≡y zN zN 0<S0 = inj₂ refl
x<Sy→x<y∨x≡y zN (sN {n} Nn) 0<SSn = inj₁ (lt-0S n)
x<Sy→x<y∨x≡y (sN {m} Nm) zN Sm<S0 =
  ⊥-elim (¬x<0 Nm (trans (sym (lt-SS m zero)) Sm<S0))
x<Sy→x<y∨x≡y (sN {m} Nm) (sN {n} Nn) Sm<SSn =
  [ (λ m<n → inj₁ (trans (lt-SS m n) m<n))
  , (λ m≡n → inj₂ (x≡y→Sx≡Sy m≡n))
  ]
  m<n∨m≡n

  where
    m<n∨m≡n : LT m n ∨ m ≡ n
    m<n∨m≡n = x<Sy→x<y∨x≡y Nm Nn (trans (sym (lt-SS m (succ n))) Sm<SSn)

x<y→y≡z→x<z : {m n o : D} → N m → N n → N o → LT m n → n ≡ o → LT m o
x<y→y≡z→x<z {m} {n} {o} Nm Nn No m<n n≡o =
  begin
    lt m o ≡⟨ subst (λ t → lt m o ≡ lt m t)
                    (sym n≡o)
                    refl
           ⟩
    lt m n ≡⟨ m<n ⟩
    true
  ∎

x≡y→y<z→x<z : {m n o : D} → N m → N n → N o → m ≡ n → LT n o → LT m o
x≡y→y<z→x<z {m} {n} {o} Nm Nn No m≡n n<o =
  begin
    lt m o ≡⟨ subst (λ t → lt m o ≡ lt t o)
                    m≡n
                    refl
           ⟩
    lt n o ≡⟨ n<o ⟩
    true
  ∎

x≥y→y>0→x-y<x : {m n : D} → N m → N n → GE m n → GT n zero → LT (m - n) m
x≥y→y>0→x-y<x Nm          zN          _     0>0  = ⊥-elim (¬x>x zN 0>0)
x≥y→y>0→x-y<x zN          (sN Nn)     0≥Sn  _    = ⊥-elim (¬S≤0 0≥Sn)
x≥y→y>0→x-y<x (sN {m} Nm) (sN {n} Nn) Sm≥Sn Sn>0 =
  begin
    lt (succ m - succ n) (succ m)
      ≡⟨ subst (λ t → lt (succ m - succ n) (succ m) ≡ lt t (succ m))
               (minus-SS m n)
               refl
      ⟩
    lt (m - n) (succ m) ≡⟨ x-y<Sx Nm Nn ⟩
    true
  ∎

------------------------------------------------------------------------------
-- Properties about LT₂

¬xy<00 : {m n : D} → N m → N n → ¬ (LT₂ m n zero zero)
¬xy<00 Nm Nn mn<00 =
  [ (λ m<0     → ⊥-elim (¬x<0 Nm m<0))
  , (λ m≡0∧n<0 → ⊥-elim (¬x<0 Nn (∧-proj₂ m≡0∧n<0)))
  ]
  mn<00

¬0Sx<00 : {m : D} → N m → ¬ (LT₂ zero (succ m) zero zero)
¬0Sx<00 Nm 0Sm<00 =
  [ (λ 0<0      → ⊥-elim (¬x<0 zN 0<0))
  , (λ 0≡0∧Sm<0 → ⊥-elim (¬x<0 (sN Nm) (∧-proj₂ 0≡0∧Sm<0)))
  ]
  0Sm<00

¬Sxy₁<0y₂ : {m n₁ n₂ : D} → N m → N n₁ → N n₂ → ¬ (LT₂ (succ m) n₁ zero n₂)
¬Sxy₁<0y₂ Nm Nn₁ Nn₂ Smn₁<0n₂ =
  [ (λ Sm<0       → ⊥-elim (¬x<0 (sN Nm) Sm<0))
  , (λ Sm≡0∧n₁<n₂ → ⊥-elim (0≠S (sym (∧-proj₁ Sm≡0∧n₁<n₂))))
  ]
  Smn₁<0n₂

x₁y<x₂0→x₁<x₂ : {m₁ n m₂ : D} → N m₁ → N n → N m₂ → LT₂ m₁ n m₂ zero → LT m₁ m₂
x₁y<x₂0→x₁<x₂ Nm₁ Nn Nm₂ m₁n<m₂zero =
  [ (λ m₁<n₁      → m₁<n₁)
  , (λ m₁≡n₁∧n<0 → ⊥-elim (¬x<0 Nn (∧-proj₂ m₁≡n₁∧n<0)))
  ]
  m₁n<m₂zero

xy₁<0y₂→x≡0∧y₁<y₂ : {m n₁ n₂ : D} → N m → N n₁ → N n₂ → LT₂ m n₁ zero n₂ →
                    m ≡ zero ∧ LT n₁ n₂
xy₁<0y₂→x≡0∧y₁<y₂ Nm Nn₁ Nn₂ mn₁<0n₂ =
  [ (λ m<0          → ⊥-elim (¬x<0 Nm m<0))
  , (λ m≡zero∧n₁<n₂ → m≡zero∧n₁<n₂)
  ]
  mn₁<0n₂

[Sx-Sy,Sy]<[Sx,Sy] :
  {m n : D} → N m → N n →
  LT₂ (succ m - succ n) (succ n) (succ m) (succ n)
[Sx-Sy,Sy]<[Sx,Sy] {m} {n} Nm Nn = inj₁ (Sx-Sy<Sx Nm Nn)

[Sx,Sy-Sx]<[Sx,Sy] : {m n : D} → N m → N n →
                     LT₂ (succ m) (succ n - succ m) (succ m) (succ n)
[Sx,Sy-Sx]<[Sx,Sy] {m} {n} Nm Nn = inj₂ (refl , Sx-Sy<Sx Nn Nm)
