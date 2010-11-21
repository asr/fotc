------------------------------------------------------------------------------
-- Properties of the inequalities (using equational reasoning)
------------------------------------------------------------------------------

module LTC-PCF.DataPCF.NatPCF.InequalitiesPCF.PropertiesPCF-ER where

open import LTC.Base
open import LTC.Base.Properties using ( x≡y→Sx≡Sy )
open import LTC.BaseER using ( subst )

open import Lib.Function using ( _$_ )
import Lib.Relation.Binary.EqReasoning
open module InequalitiesPCF-ER =
  Lib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

open import LTC-PCF.DataPCF.NatPCF
  using ( _+_ ; _-_
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF
  using ( _<_ ; <-aux₁ ; <-aux₂ ; <-h
        ; _≤_
        ; GE ; GT ; LE ; LT ; NGT ; NLE ; NLT
        ; LT₂
        )
open import LTC-PCF.DataPCF.NatPCF.PropertiesPCF-ER
  using ( +-N ; minus-N
        ; +-Sx
        ; +-comm
        ; +-rightIdentity
        ; minus-0S ; minus-SS ; minus-x0
        )

------------------------------------------------------------------------------

private

  -- Before to prove some properties for 'lt i j' it is convenient
  -- to descompose the behavior of the function step by step.

  -- Initially, we define the possible states (<-s₁,
  -- <-s₂, ...). Then we write down the proof for
  -- the execution step from the state p to the state q
  --
  -- (e.g. s₁→s₂ : (m n : D) → <-s₂ m n → <-s₃ m n).

  -- The terms lt-00, lt-0S, lt-S0, and lt-S>S show the use of the
  -- states <-s₁, <-s₂, ..., and the proofs associated with the
  -- execution steps.

  ----------------------------------------------------------------------
  -- The steps of lt

  -- The conversion rule fix-f is applied.
  <-s₁ : D → D → D
  <-s₁ d e = <-h (fix <-h) ∙ d ∙ e

  -- Definition of <-h.
  <-s₂ : D → D → D
  <-s₂ d e = lam (<-aux₂ (fix <-h)) ∙ d ∙ e

  -- Beta application.
  <-s₃ : D → D → D
  <-s₃ d e = <-aux₂ (fix <-h) d ∙ e

  -- Definition of lt-aux₂.
  <-s₄ : D → D → D
  <-s₄ d e = lam (<-aux₁ d (fix <-h)) ∙ e

  -- Beta application.
  <-s₅ : D → D → D
  <-s₅ d e = <-aux₁ d (fix <-h) e

  -- Definition lt-aux₁.
  <-s₆ : D → D → D
  <-s₆ d e = if (isZero e) then false
                else (if (isZero d) then true
                         else ((fix <-h) ∙ (pred d) ∙ (pred e)))

  -- Reduction 'isZero e ≡ b'.
  <-s₇ : D → D → D → D
  <-s₇ d e b = if b then false
                  else (if (isZero d) then true
                           else ((fix <-h) ∙ (pred d) ∙ (pred e)))

  -- Reduction 'isZero e ≡ false'.
  <-s₈ : D → D → D
  <-s₈ d e = if (isZero d) then true
                 else ((fix <-h) ∙ (pred d) ∙ (pred e))

  -- Reduction 'isZero d ≡ b'.
  <-s₉ : D → D → D → D
  <-s₉ d e b = if b then true
                  else ((fix <-h) ∙ (pred d) ∙ (pred e))

  -- Reduction 'isZero d ≡ false'.
  <-s₁₀ : D → D → D
  <-s₁₀ d e = (fix <-h) ∙ (pred d) ∙ (pred e)

  -- Reduction 'pred (succ d) ≡ d'.
  <-s₁₁ : D → D → D
  <-s₁₁ d e = (fix <-h) ∙ d ∙ (pred e)

  -- Reduction 'pred (succ e) ≡ e'.
  <-s₁₂ : D → D → D
  <-s₁₂ d e = (fix <-h) ∙ d ∙ e

  ----------------------------------------------------------------------
  -- The execution steps

  {-
    To prove the execution steps (e.g. s₃→s₄ : (m n : D) → <-s₃ m n → <-s₄ m n),
    we usually need to prove that

                         C [m] ≡ C [n]    (1)

    given that
                             m ≡ n,       (2)

    where (2) is a conversion rule usually.

    We prove (1) using

    subst : {A : Set}(P : A → Set){x y : A} → x ≡ y → P x → P y

    where
      - P is given by λ t → C [m] ≡ C [t],
      - x ≡ y is given m ≡ n, and
      - P x is given by C [m] ≡ C [m] (i.e. refl).
  -}

  -- Application of the conversion rule fix-f.
  initial→s₁ : (d e : D) → fix <-h ∙ d ∙ e ≡ <-s₁ d e
  initial→s₁ d e = subst (λ t → fix <-h ∙ d ∙ e ≡ t ∙ d ∙ e) (fix-f <-h) refl

  -- The definition of <-h.
  s₁→s₂ : (d e : D) → <-s₁ d e ≡ <-s₂ d e
  s₁→s₂ d e = refl

  -- Beta application.
  s₂→s₃ : (d e : D) → <-s₂ d e ≡ <-s₃ d e
  s₂→s₃ d e = subst (λ t → lam (<-aux₂ (fix <-h)) ∙ d ∙ e ≡ t ∙ e)
                    (beta (<-aux₂ (fix <-h)) d)
                    refl

  -- Definition of lt-aux₂
  s₃→s₄ : (d e : D) → <-s₃ d e ≡ <-s₄ d e
  s₃→s₄ d e = refl

  -- Beta application.
  s₄→s₅ : (d e : D) → <-s₄ d e ≡ <-s₅ d e
  s₄→s₅ d e = beta (<-aux₁ d (fix <-h)) e

  -- Definition of lt-aux₁.
  s₅→s₆ : (d e : D) → <-s₅ d e ≡ <-s₆ d e
  s₅→s₆ d e = refl

  -- Reduction 'isZero e ≡ b' using that proof.
  s₆→s₇ : (d e b : D) → isZero e ≡ b → <-s₆ d e ≡ <-s₇ d e b
  s₆→s₇ d e b prf = subst (λ t → <-s₆ d e ≡ <-s₇ d e t) prf refl

  -- Reduction of 'isZero e ≡ true' using the conversion rule if-true.
  s₇→end : (d e : D) → <-s₇ d e true ≡ false
  s₇→end _ _ = if-true false

  -- Reduction of 'isZero e ≡ false ...' using the conversion rule if-false.
  s₇→s₈ : (d e : D) → <-s₇ d e false ≡ <-s₈ d e
  s₇→s₈ d e = if-false (<-s₈ d e)

  -- Reduction 'isZero d ≡ b' using that proof.
  s₈→s₉ : (d e b : D) → isZero d ≡ b → <-s₈ d e ≡ <-s₉ d e b
  s₈→s₉ d e b prf = subst (λ t → <-s₈ d e ≡ <-s₉ d e t) prf refl

  -- Reduction of 'isZero d ≡ true' using the conversion rule if-true.
  s₉→end : (d e : D) → <-s₉ d e true ≡ true
  s₉→end _ _ = if-true true

  -- Reduction of 'isZero d ≡ false ...' using the conversion rule if-false.
  s₉→s₁₀ : (d e : D) → <-s₉ d e false ≡ <-s₁₀ d e
  s₉→s₁₀ d e = if-false (<-s₁₀ d e)

  -- Reduction 'pred (succ d) ≡ d' using the conversion rule pred-S.
  s₁₀→s₁₁ : (d e : D) → <-s₁₀ (succ d) e ≡ <-s₁₁ d e
  s₁₀→s₁₁ d e = subst (λ t → <-s₁₀ (succ d) e ≡ <-s₁₁ t e) (pred-S d) refl

  -- Reduction 'pred (succ e) ≡ e' using the conversion rule pred-S.
  s₁₁→s₁₂ : (d e : D) → <-s₁₁ d (succ e) ≡ <-s₁₂ d e
  s₁₁→s₁₂ d e = subst (λ t → <-s₁₁ d (succ e) ≡ <-s₁₂ d t) (pred-S e) refl

------------------------------------------------------------------------------

<-00 : NLT zero zero
<-00 =
  begin
    fix <-h ∙ zero ∙ zero ≡⟨ initial→s₁ zero zero ⟩
    <-s₁ zero zero        ≡⟨ s₁→s₂ zero zero ⟩
    <-s₂ zero zero        ≡⟨ s₂→s₃ zero zero ⟩
    <-s₃ zero zero        ≡⟨ s₃→s₄ zero zero ⟩
    <-s₄ zero zero        ≡⟨ s₄→s₅ zero zero ⟩
    <-s₅ zero zero        ≡⟨ s₅→s₆ zero zero ⟩
    <-s₆ zero zero        ≡⟨ s₆→s₇ zero zero true isZero-0 ⟩
    <-s₇ zero zero true   ≡⟨ s₇→end zero zero ⟩
    false
    ∎

<-0S : (d : D) → LT zero (succ d)
<-0S d =
  begin
    fix <-h ∙ zero ∙ (succ d) ≡⟨ initial→s₁ zero (succ d) ⟩
    <-s₁ zero (succ d)        ≡⟨ s₁→s₂ zero (succ d) ⟩
    <-s₂ zero (succ d)        ≡⟨ s₂→s₃ zero (succ d) ⟩
    <-s₃ zero (succ d)        ≡⟨ s₃→s₄ zero (succ d) ⟩
    <-s₄ zero (succ d)        ≡⟨ s₄→s₅ zero (succ d) ⟩
    <-s₅ zero (succ d)        ≡⟨ s₅→s₆ zero (succ d) ⟩
    <-s₆ zero (succ d)        ≡⟨ s₆→s₇ zero (succ d) false (isZero-S d) ⟩
    <-s₇ zero (succ d) false  ≡⟨ s₇→s₈ zero (succ d) ⟩
    <-s₈ zero (succ d)        ≡⟨ s₈→s₉ zero (succ d) true isZero-0 ⟩
    <-s₉ zero (succ d) true   ≡⟨ s₉→end zero (succ d) ⟩
    true
  ∎

<-S0 : (d : D) → NLT (succ d) zero
<-S0 d =
  begin
    fix <-h ∙ (succ d) ∙ zero ≡⟨ initial→s₁ (succ d) zero ⟩
    <-s₁ (succ d) zero        ≡⟨ s₁→s₂ (succ d) zero ⟩
    <-s₂ (succ d) zero        ≡⟨ s₂→s₃ (succ d) zero ⟩
    <-s₃ (succ d) zero        ≡⟨ s₃→s₄ (succ d) zero ⟩
    <-s₄ (succ d) zero        ≡⟨ s₄→s₅ (succ d) zero ⟩
    <-s₅ (succ d) zero        ≡⟨ s₅→s₆ (succ d) zero ⟩
    <-s₆ (succ d) zero        ≡⟨ s₆→s₇ (succ d) zero true isZero-0 ⟩
    <-s₇ (succ d) zero true   ≡⟨ s₇→end (succ d) zero ⟩
    false
  ∎

<-SS : (d e : D) → (succ d) < (succ e) ≡ d < e
<-SS d e =
  begin
    fix <-h ∙ (succ d) ∙ (succ e) ≡⟨ initial→s₁ (succ d) (succ e) ⟩
    <-s₁ (succ d) (succ e)        ≡⟨ s₁→s₂ (succ d) (succ e) ⟩
    <-s₂ (succ d) (succ e)        ≡⟨ s₂→s₃ (succ d) (succ e) ⟩
    <-s₃ (succ d) (succ e)        ≡⟨ s₃→s₄ (succ d) (succ e) ⟩
    <-s₄ (succ d) (succ e)        ≡⟨ s₄→s₅ (succ d) (succ e) ⟩
    <-s₅ (succ d) (succ e)        ≡⟨ s₅→s₆ (succ d) (succ e) ⟩
    <-s₆ (succ d) (succ e)        ≡⟨ s₆→s₇ (succ d) (succ e)
                                           false (isZero-S e)
                                  ⟩
    <-s₇ (succ d) (succ e) false  ≡⟨ s₇→s₈ (succ d) (succ e) ⟩
    <-s₈ (succ d) (succ e)        ≡⟨ s₈→s₉ (succ d) (succ e)
                                           false (isZero-S d)
                                  ⟩
    <-s₉ (succ d) (succ e) false  ≡⟨ s₉→s₁₀ (succ d) (succ e) ⟩
    <-s₁₀ (succ d) (succ e)       ≡⟨ s₁₀→s₁₁ d (succ e) ⟩
    <-s₁₁ d (succ e)              ≡⟨ s₁₁→s₁₂ d e ⟩
    <-s₁₂ d e                     ≡⟨ refl ⟩
    d < e
  ∎

x≥0 : {n : D} → N n → GE n zero
x≥0 zN          = <-0S zero
x≥0 (sN {n} Nn) = <-0S $ succ n

0≤x : {n : D} → N n → LE zero n
0≤x Nn = x≥0 Nn

¬x<0 : {n : D} → N n → ¬ (LT n zero)
¬x<0 zN 0<0           = true≠false $ trans (sym 0<0) (<-00)
¬x<0 (sN {n} Nn) Sn<0 = true≠false $ trans (sym Sn<0) (<-S0 n)

0≯x : {n : D} → N n → NGT zero n
0≯x zN          = <-00
0≯x (sN {n} Nn) = <-S0 n

¬0>x : {n : D} → N n → ¬ (GT zero n)
¬0>x Nn 0>n = true≠false $ trans (sym 0>n) $ 0≯x Nn

x≰x : {n : D} → N n → NLT n n
x≰x zN          = <-00
x≰x (sN {n} Nn) = trans (<-SS n n) (x≰x Nn)

S≰0 : {n : D} → N n → NLE (succ n) zero
S≰0 zN          = x≰x (sN zN)
S≰0 (sN {n} Nn) = trans (<-SS (succ n) zero) (<-S0 n)

¬S≤0 : {n : D} → N n → ¬ (LE (succ n) zero)
¬S≤0 {d} Nn Sn≤0 = true≠false $ trans (sym Sn≤0) (S≰0 Nn)

¬0≥S : {n : D} → N n → ¬ (GE zero (succ n))
¬0≥S Nn 0≥Sn = ¬S≤0 Nn 0≥Sn

x<Sx : {n : D} → N n → LT n (succ n)
x<Sx zN          = <-0S zero
x<Sx (sN {n} Nn) = trans (<-SS n (succ n)) (x<Sx Nn)

¬x<x : {m : D} → N m → ¬ (LT m m)
¬x<x zN          0<0   = ⊥-elim $ true≠false $ trans (sym 0<0) <-00
¬x<x (sN {m} Nm) Sm<Sm = ⊥-elim $ ¬x<x Nm (trans (sym $ <-SS m m) Sm<Sm)

¬x>x : {m : D} → N m → ¬ (GT m m)
¬x>x Nm = ¬x<x Nm

x≤x : {m : D} → N m → LE m m
x≤x zN          = <-0S zero
x≤x (sN {m} Nm) = trans (<-SS m (succ m)) (x≤x Nm)

x≥y→x≮y : {m n : D} → N m → N n → GE m n → NLT m n
x≥y→x≮y zN          zN          _     = x≰x zN
x≥y→x≮y zN          (sN Nn)     0≥Sn  = ⊥-elim $ ¬0≥S Nn 0≥Sn
x≥y→x≮y (sN {m} Nm) zN          _     = <-S0 m
x≥y→x≮y (sN {m} Nm) (sN {n} Nn) Sm≥Sn =
  trans (<-SS m n) (x≥y→x≮y Nm Nn (trans (sym $ <-SS n (succ m)) Sm≥Sn))

x>y∨x≤y : {m n : D} → N m → N n → GT m n ∨ LE m n
x>y∨x≤y zN          Nn          = inj₂ $ x≥0 Nn
x>y∨x≤y (sN {m} Nm) zN          = inj₁ $ <-0S m
x>y∨x≤y (sN {m} Nm) (sN {n} Nn) =
  [ (λ m>n → inj₁ (trans (<-SS n m) m>n))
  , (λ m≤n → inj₂ (trans (<-SS m (succ n)) m≤n))
  ] (x>y∨x≤y Nm Nn)

x<y∨x≥y : {m n : D} → N m → N n → LT m n ∨ GE m n
x<y∨x≥y Nm Nn = x>y∨x≤y Nn Nm

x≡y→x≤y : {m n : D}{Nm : N m}{Nn : N n} → m ≡ n → LE m n
x≡y→x≤y {Nm = Nm} refl = x≤x Nm

x<y→x≤y : {m n : D} → N m → N n → LT m n → LE m n
x<y→x≤y Nm zN          m<0            = ⊥-elim $ ¬x<0 Nm m<0
x<y→x≤y zN (sN {n} Nn) _              = <-0S $ succ n
x<y→x≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn =
  begin
    (succ m) < (succ (succ n)) ≡⟨ <-SS m (succ n) ⟩
    m < (succ n)               ≡⟨ x<y→x≤y Nm Nn (trans (sym $ <-SS m n) Sm<Sn) ⟩
    true
  ∎

x<y→Sx≤y : {m n : D} → N m → N n → LT m n → LE (succ m) n
x<y→Sx≤y Nm zN               m<0       = ⊥-elim $ ¬x<0 Nm m<0
x<y→Sx≤y zN          (sN {n} Nn) _     = trans (<-SS zero (succ n)) (<-0S n)
x<y→Sx≤y (sN {m} Nm) (sN {n} Nn) Sm<Sn = trans (<-SS (succ m) (succ n)) Sm<Sn

Sx≤y→x<y : {m n : D} → N m → N n → LE (succ m) n → LT m n
Sx≤y→x<y Nm          zN          Sm≤0   = ⊥-elim $ ¬S≤0 Nm Sm≤0
Sx≤y→x<y zN          (sN {n} Nn) _      = <-0S n
Sx≤y→x<y (sN {m} Nm) (sN {n} Nn) SSm≤Sn =
  trans (<-SS m n) (Sx≤y→x<y Nm Nn (trans (sym $ <-SS (succ m) (succ n))
                                           SSm≤Sn))

<-trans : {m n o : D} → N m → N n → N o → LT m n → LT n o → LT m o
<-trans zN          zN           _          0<0   _    = ⊥-elim $ ¬x<0 zN 0<0
<-trans zN          (sN Nn)     zN          _     Sn<0 = ⊥-elim $ ¬x<0 (sN Nn) Sn<0
<-trans zN          (sN Nn)     (sN {o} No) _     _    = <-0S o
<-trans (sN Nm)     Nn          zN          _     n<0  = ⊥-elim $ ¬x<0 Nn n<0
<-trans (sN Nm)     zN          (sN No)     Sm<0  _    = ⊥-elim $ ¬x<0 (sN Nm) Sm<0
<-trans (sN {m} Nm) (sN {n} Nn) (sN {o} No) Sm<Sn Sn<So =
  begin
    (succ m) < (succ o) ≡⟨ <-SS m o ⟩
    m < o               ≡⟨ <-trans Nm Nn No
                           (trans (sym $ <-SS m n) Sm<Sn)
                           (trans (sym $ <-SS n o) Sn<So)
                        ⟩
    true
  ∎

≤-trans : {m n o : D} → N m → N n → N o → LE m n → LE n o → LE m o
≤-trans zN      Nn              No          _     _     = 0≤x No
≤-trans (sN Nm) zN              No          Sm≤0  _     = ⊥-elim $ ¬S≤0 Nm Sm≤0
≤-trans (sN Nm) (sN Nn)         zN          _     Sn≤0  = ⊥-elim $ ¬S≤0 Nn Sn≤0
≤-trans (sN {m} Nm) (sN {n} Nn) (sN {o} No) Sm≤Sn Sn≤So =
  trans (<-SS m (succ o))
        (≤-trans Nm Nn No
                 (trans (sym $ <-SS m (succ n)) Sm≤Sn)
                 (trans (sym $ <-SS n (succ o)) Sn≤So))

Sx≤Sy→x≤y : {m n : D} → LE (succ m) (succ n) → LE m n
Sx≤Sy→x≤y {m} {n} Sm≤Sn = trans (sym $ <-SS m (succ n)) Sm≤Sn

x≤x+y : {m n : D} → N m → N n → LE m (m + n)
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

x-y<Sx : {m n : D} → N m → N n → LT (m - n) (succ m)
x-y<Sx {m} Nm zN =
  begin
    (m - zero) < (succ m) ≡⟨ subst (λ t → (m - zero) < (succ m) ≡
                                          t  < (succ m))
                                    (minus-x0 m)
                                    refl
                           ⟩
    m < (succ m)          ≡⟨ x<Sx Nm ⟩
    true
  ∎

x-y<Sx zN (sN {n} Nn) =
  begin
    (zero - succ n) < (succ zero)
      ≡⟨ subst (λ t → (zero - succ n) < (succ zero) ≡ t < (succ zero))
               (minus-0S Nn)
               refl
      ⟩
    zero < succ zero ≡⟨ <-0S zero ⟩
    true
  ∎

x-y<Sx (sN {m} Nm) (sN {n} Nn) =
  begin
    (succ m - succ n) < (succ (succ m))
      ≡⟨ subst (λ t → (succ m - succ n) < (succ (succ m)) ≡
                      t < (succ (succ m)))
               (minus-SS Nm Nn)
               refl
      ⟩
    (m - n) < (succ (succ m))
      ≡⟨ <-trans (minus-N Nm Nn) (sN Nm) (sN (sN Nm))
                 (x-y<Sx Nm Nn) (x<Sx (sN Nm))
      ⟩
    true
  ∎

Sx-Sy<Sx : {m n : D} → N m → N n → LT (succ m - succ n) (succ m)
Sx-Sy<Sx {m} {n} Nm Nn =
  begin
    (succ m - succ n) < (succ m) ≡⟨ subst (λ t → (succ m - succ n) <
                                                     (succ m) ≡
                                                  t < (succ m))
                                           (minus-SS Nm Nn)
                                           refl
                                  ⟩
    (m - n) < (succ m)           ≡⟨ x-y<Sx Nm Nn ⟩
    true
    ∎

x>y→x-y+y≡x : {m n : D} → N m → N n → GT m n → (m - n) + n ≡ m
x>y→x-y+y≡x zN          Nn 0>n  = ⊥-elim $ ¬0>x Nn 0>n
x>y→x-y+y≡x (sN {m} Nm) zN Sm>0 = trans (+-rightIdentity (minus-N (sN Nm) zN))
                                        (minus-x0 (succ m))
x>y→x-y+y≡x (sN {m} Nm) (sN {n} Nn) Sm>Sn =
  begin
    (succ m - succ n) + succ n ≡⟨ subst (λ t → (succ m - succ n) + succ n ≡
                                               t + succ n)
                                        (minus-SS Nm Nn)
                                        refl
                               ⟩
    (m - n) + succ n           ≡⟨ +-comm (minus-N Nm Nn) (sN Nn) ⟩
    succ n + (m - n)           ≡⟨ +-Sx n (m - n) ⟩
    succ (n + (m - n))         ≡⟨ subst (λ t → succ (n + (m - n)) ≡ succ t)
                                        (+-comm Nn (minus-N Nm Nn))
                                        refl
                               ⟩
    succ ((m - n) + n)         ≡⟨ subst (λ t → succ ((m - n) + n) ≡ succ t)
                                        (x>y→x-y+y≡x Nm Nn
                                             (trans (sym $ <-SS n m) Sm>Sn))
                                        refl
                               ⟩
    succ m
  ∎

x≤y→y-x+x≡y : {m n : D} → N m → N n → LE m n → (n - m) + m ≡ n
x≤y→y-x+x≡y {n = n} zN      Nn 0≤n  = trans (+-rightIdentity (minus-N Nn zN))
                                            (minus-x0 n)
x≤y→y-x+x≡y         (sN Nm) zN Sm≤0 = ⊥-elim $ ¬S≤0 Nm Sm≤0
x≤y→y-x+x≡y (sN {m} Nm) (sN {n} Nn) Sm≤Sn =
  begin
    (succ n - succ m) + succ m ≡⟨ subst (λ t → (succ n - succ m) + succ m ≡
                                               t + succ m)
                                        (minus-SS Nn Nm)
                                        refl
                               ⟩
    (n - m) + succ m           ≡⟨ +-comm (minus-N Nn Nm) (sN Nm) ⟩
    succ m + (n - m)           ≡⟨ +-Sx m (n - m) ⟩
    succ (m + (n - m))         ≡⟨ subst (λ t → succ (m + (n - m)) ≡ succ t)
                                        (+-comm Nm (minus-N Nn Nm))
                                        refl
                               ⟩
    succ ((n - m) + m)         ≡⟨ subst (λ t → succ ((n - m) + m) ≡ succ t)
                                        (x≤y→y-x+x≡y Nm Nn
                                             (trans (sym $ <-SS m (succ n))
                                                    Sm≤Sn))
                                        refl
                               ⟩
    succ n
  ∎

x<y→x<Sy : {m n : D} → N m → N n → LT m n → LT m (succ n)
x<y→x<Sy Nm          zN          m<0   = ⊥-elim $ ¬x<0 Nm m<0
x<y→x<Sy zN          (sN {n} Nn) 0<Sn  = <-0S $ succ n
x<y→x<Sy (sN {m} Nm) (sN {n} Nn) Sm<Sn =
  trans (<-SS m (succ n)) (x<y→x<Sy Nm Nn (trans (sym $ <-SS m n) Sm<Sn))

x<Sy→x<y∨x≡y : {m n : D} → N m → N n → LT m (succ n) → LT m n ∨ m ≡ n
x<Sy→x<y∨x≡y zN zN 0<S0 = inj₂ refl
x<Sy→x<y∨x≡y zN (sN {n} Nn) 0<SSn = inj₁ (<-0S n)
x<Sy→x<y∨x≡y (sN {m} Nm) zN Sm<S0 =
  ⊥-elim $ ¬x<0 Nm (trans (sym $ <-SS m zero) Sm<S0)
x<Sy→x<y∨x≡y (sN {m} Nm) (sN {n} Nn) Sm<SSn =
  [ (λ m<n → inj₁ (trans (<-SS m n) m<n))
  , (λ m≡n → inj₂ (x≡y→Sx≡Sy m≡n))
  ]
  m<n∨m≡n

  where
    m<n∨m≡n : LT m n ∨ m ≡ n
    m<n∨m≡n = x<Sy→x<y∨x≡y Nm Nn (trans (sym $ <-SS m (succ n)) Sm<SSn)

x<y→y≡z→x<z : {m n o : D} → N m → N n → N o → LT m n → n ≡ o → LT m o
x<y→y≡z→x<z {m} {n} {o} Nm Nn No m<n n≡o =
  begin
    m < o ≡⟨ subst (λ t → m < o ≡ m < t)
                    (sym n≡o)
                    refl
           ⟩
    m < n ≡⟨ m<n ⟩
    true
  ∎

x≡y→y<z→x<z : {m n o : D} → N m → N n → N o → m ≡ n → LT n o → LT m o
x≡y→y<z→x<z {m} {n} {o} Nm Nn No m≡n n<o =
  begin
    m < o ≡⟨ subst (λ t → m < o ≡ t < o)
                    m≡n
                    refl
           ⟩
    n < o ≡⟨ n<o ⟩
    true
  ∎

x≥y→y>0→x-y<x : {m n : D} → N m → N n → GE m n → GT n zero → LT (m - n) m
x≥y→y>0→x-y<x Nm          zN          _     0>0  = ⊥-elim $ ¬x>x zN 0>0
x≥y→y>0→x-y<x zN          (sN Nn)     0≥Sn  _    = ⊥-elim $ ¬S≤0 Nn 0≥Sn
x≥y→y>0→x-y<x (sN {m} Nm) (sN {n} Nn) Sm≥Sn Sn>0 =
  begin
    (succ m - succ n) < (succ m)
      ≡⟨ subst (λ t → (succ m - succ n) < (succ m) ≡ t < (succ m))
               (minus-SS Nm Nn)
               refl
      ⟩
    (m - n) < (succ m) ≡⟨ x-y<Sx Nm Nn ⟩
    true
  ∎

------------------------------------------------------------------------------
-- Properties about LT₂

¬xy<00 : {m n : D} → N m → N n → ¬ (LT₂ m n zero zero)
¬xy<00 Nm Nn mn<00 =
  [ (λ m<0     → ⊥-elim $ ¬x<0 Nm m<0)
  , (λ m≡0∧n<0 → ⊥-elim $ ¬x<0 Nn (∧-proj₂ m≡0∧n<0))
  ]
  mn<00

¬0Sx<00 : {m : D} → N m → ¬ (LT₂ zero (succ m) zero zero)
¬0Sx<00 Nm 0Sm<00 =
  [ (λ 0<0      → ⊥-elim $ ¬x<0 zN 0<0)
  , (λ 0≡0∧Sm<0 → ⊥-elim $ ¬x<0 (sN Nm) (∧-proj₂ 0≡0∧Sm<0))
  ]
  0Sm<00

¬Sxy₁<0y₂ : {m n₁ n₂ : D} → N m → N n₁ → N n₂ → ¬ (LT₂ (succ m) n₁ zero n₂)
¬Sxy₁<0y₂ Nm Nn₁ Nn₂ Smn₁<0n₂ =
  [ (λ Sm<0       → ⊥-elim $ ¬x<0 (sN Nm) Sm<0)
  , (λ Sm≡0∧n₁<n₂ → ⊥-elim $ 0≠S $ sym $ ∧-proj₁ Sm≡0∧n₁<n₂)
  ]
  Smn₁<0n₂

x₁y<x₂0→x₁<x₂ : {m₁ n m₂ : D} → N m₁ → N n → N m₂ → LT₂ m₁ n m₂ zero → LT m₁ m₂
x₁y<x₂0→x₁<x₂ Nm₁ Nn Nm₂ m₁n<m₂zero =
  [ (λ m₁<n₁     → m₁<n₁)
  , (λ m₁≡n₁∧n<0 → ⊥-elim $ ¬x<0 Nn (∧-proj₂ m₁≡n₁∧n<0))
  ]
  m₁n<m₂zero

xy₁<0y₂→x≡0∧y₁<y₂ : {m n₁ n₂ : D} → N m → N n₁ → N n₂ → LT₂ m n₁ zero n₂ →
                    m ≡ zero ∧ LT n₁ n₂
xy₁<0y₂→x≡0∧y₁<y₂ Nm Nn₁ Nn₂ mn₁<0n₂ =
  [ (λ m<0          → ⊥-elim $ ¬x<0 Nm m<0)
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
