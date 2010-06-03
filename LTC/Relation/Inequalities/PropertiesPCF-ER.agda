------------------------------------------------------------------------------
-- Properties of the inequalities (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Relation.Inequalities.PropertiesPCF-ER where

open import LTC.Minimal
open import LTC.MinimalER

open import LTC.Function.ArithmeticPCF
open import LTC.Function.Arithmetic.PropertiesPCF-ER
open import LTC.Relation.Equalities.PropertiesER
open import LTC.Relation.InequalitiesPCF
open import LTC.Data.N

open import MyStdLib.Data.Sum
open import MyStdLib.Function
import MyStdLib.Relation.Binary.EqReasoning
open module IPER = MyStdLib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

------------------------------------------------------------------------------

private
  ----------------------------------------------------------------------
  -- The steps of lt

  --TODO : Doc. See LTC-PLPV

  -- The conversion rule 'cFix' is applied.
  <-s₁ : D → D → D
  <-s₁ d e = lth (fix lth) ∙ d ∙ e

  -- Definition of lth.
  <-s₂ : D → D → D
  <-s₂ d e = lam (lt-aux₂ (fix lth)) ∙ d ∙ e

  -- cBeta application.
  <-s₃ : D → D → D
  <-s₃ d e = lt-aux₂ (fix lth) d ∙ e

  -- Definition of lt-aux₂.
  <-s₄ : D → D → D
  <-s₄ d e = lam (lt-aux₁ d (fix lth)) ∙ e

  -- cBeta application.
  <-s₅ : D → D → D
  <-s₅ d e = lt-aux₁ d (fix lth) e

  -- Definition lt-aux₁.
  <-s₆ : D → D → D
  <-s₆ d e = if (isZero e) then false
                else (if (isZero d) then true
                         else ((fix lth) ∙ (pred d) ∙ (pred e)))

  -- Reduction 'isZero e ≡ b'.
  <-s₇ : D → D → D → D
  <-s₇ d e b = if b then false
                  else (if (isZero d) then true
                           else ((fix lth) ∙ (pred d) ∙ (pred e)))

  -- Reduction 'isZero e ≡ false'.
  <-s₈ : D → D → D
  <-s₈ d e = if (isZero d) then true
                 else ((fix lth) ∙ (pred d) ∙ (pred e))

  -- Reduction 'isZero d ≡ b'.
  <-s₉ : D → D → D → D
  <-s₉ d e b = if b then true
                  else ((fix lth) ∙ (pred d) ∙ (pred e))

  -- Reduction 'isZero d ≡ false'.
  <-s₁₀ : D → D → D
  <-s₁₀ d e = (fix lth) ∙ (pred d) ∙ (pred e)

  -- Reduction 'pred (succ d) ≡ d'.
  <-s₁₁ : D → D → D
  <-s₁₁ d e = (fix lth) ∙ d ∙ (pred e)

  -- Reduction 'pred (succ e) ≡ e'.
  <-s₁₂ : D → D → D
  <-s₁₂ d e = (fix lth) ∙ d ∙ e

  ----------------------------------------------------------------------
  -- The execution steps

  --TODO : Doc. See LTC-PLPV

  -- Application of the conversion rule 'cFix'.
  initial→s₁ : (d e : D) → fix lth ∙ d ∙ e  ≡ <-s₁ d e
  initial→s₁ d e = subst (λ t → t ∙ d ∙ e  ≡ lth (fix lth) ∙ d ∙ e )
                         (sym (cFix lth ))
                         refl

  -- The definition of lth.
  s₁→s₂ : (d e : D) → <-s₁ d e ≡ <-s₂ d e
  s₁→s₂ d e = refl

  -- cBeta application.
  s₂→s₃ : (d e : D) → <-s₂ d e ≡ <-s₃ d e
  s₂→s₃ d e = subst (λ t → lam (lt-aux₂ (fix lth)) ∙ d ∙ e ≡ t ∙ e)
                    (cBeta (lt-aux₂ (fix lth)) d)
                    refl

  -- Definition of lt-aux₂
  s₃→s₄ : (d e : D) → <-s₃ d e ≡ <-s₄ d e
  s₃→s₄ d e = refl

  -- cBeta application.
  s₄→s₅ : (d e : D) → <-s₄ d e ≡ <-s₅ d e
  s₄→s₅ d e = cBeta (lt-aux₁ d (fix lth)) e

  -- Definition of lt-aux₁.
  s₅→s₆ : (d e : D) → <-s₅ d e ≡ <-s₆ d e
  s₅→s₆ d e = refl

  -- Reduction 'isZero e ≡ b' using that proof.
  s₆→s₇ : (d e b : D) → isZero e ≡ b → <-s₆ d e ≡ <-s₇ d e b
  s₆→s₇ d e b prf = subst (λ t → <-s₇ d e t ≡ <-s₇ d e b )
                          (sym prf)
                          refl

  -- Reduction of 'isZero e ≡ true' using the conversion rule cB₁.
  s₇→end : (d e : D) → <-s₇ d e true ≡ false
  s₇→end _ _ = cB₁ false

  -- Reduction of 'isZero e ≡ false ...' using the conversion rule cB₂.
  s₇→s₈ : (d e : D) → <-s₇ d e false ≡ <-s₈ d e
  s₇→s₈ d e = cB₂ (<-s₈ d e)

  -- Reduction 'isZero d ≡ b' using that proof.
  s₈→s₉ : (d e b : D) → isZero d ≡ b → <-s₈ d e ≡ <-s₉ d e b
  s₈→s₉ d e b prf = subst (λ t → <-s₉ d e t ≡ <-s₉ d e b )
                          (sym prf)
                          refl

  -- Reduction of 'isZero d ≡ true' using the conversion rule cB₁.
  s₉→end : (d e : D) → <-s₉ d e true ≡ true
  s₉→end _ _ = cB₁ true

  -- Reduction of 'isZero d ≡ false ...' using the conversion rule cB₂.
  s₉→s₁₀ : (d e : D) → <-s₉ d e false ≡ <-s₁₀ d e
  s₉→s₁₀ d e = cB₂ (<-s₁₀ d e)

  -- Reduction 'pred (succ d) ≡ d' using the conversion rule cP₂.
  s₁₀→s₁₁ : (d e : D) → <-s₁₀ (succ d) e  ≡ <-s₁₁ d e
  s₁₀→s₁₁ d e = subst (λ t → <-s₁₁ t e ≡ <-s₁₁ d e)
                      (sym (cP₂ d ))
                      refl

  -- Reduction 'pred (succ e) ≡ e' using the conversion rule 'cP₂'.
  s₁₁→s₁₂ : (d e : D) → <-s₁₁ d (succ e)  ≡ <-s₁₂ d e
  s₁₁→s₁₂ d e = subst (λ t → <-s₁₂ d t ≡ <-s₁₂ d e)
                      (sym (cP₂ e ))
                      refl

------------------------------------------------------------------------------

lt-00 : GE zero zero -- lt zero zero ≡ false
lt-00 =
  begin
    fix lth ∙ zero ∙ zero ≡⟨ initial→s₁ zero zero ⟩
    <-s₁ zero zero        ≡⟨ s₁→s₂ zero zero ⟩
    <-s₂ zero zero        ≡⟨ s₂→s₃ zero zero ⟩
    <-s₃ zero zero        ≡⟨ s₃→s₄ zero zero ⟩
    <-s₄ zero zero        ≡⟨ s₄→s₅ zero zero ⟩
    <-s₅ zero zero        ≡⟨ s₅→s₆ zero zero ⟩
    <-s₆ zero zero        ≡⟨ s₆→s₇ zero zero true cZ₁ ⟩
    <-s₇ zero zero true   ≡⟨ s₇→end zero zero ⟩
    false
    ∎

lt-0S : (d : D) → LT zero (succ d)
lt-0S d =
  begin
    fix lth ∙ zero ∙ (succ d) ≡⟨ initial→s₁ zero (succ d) ⟩
    <-s₁ zero (succ d)        ≡⟨ s₁→s₂ zero (succ d) ⟩
    <-s₂ zero (succ d)        ≡⟨ s₂→s₃ zero (succ d) ⟩
    <-s₃ zero (succ d)        ≡⟨ s₃→s₄ zero (succ d) ⟩
    <-s₄ zero (succ d)        ≡⟨ s₄→s₅ zero (succ d) ⟩
    <-s₅ zero (succ d)        ≡⟨ s₅→s₆ zero (succ d) ⟩
    <-s₆ zero (succ d)        ≡⟨ s₆→s₇ zero (succ d) false (cZ₂ d) ⟩
    <-s₇ zero (succ d) false  ≡⟨ s₇→s₈ zero (succ d) ⟩
    <-s₈ zero (succ d)        ≡⟨ s₈→s₉ zero (succ d) true cZ₁ ⟩
    <-s₉ zero (succ d) true   ≡⟨ s₉→end zero (succ d) ⟩
    true
  ∎

lt-S0 : (d : D) → GE (succ d) zero -- lt (succ d) zero ≡ false
lt-S0 d =
  begin
    fix lth ∙ (succ d) ∙ zero ≡⟨ initial→s₁ (succ d) zero ⟩
    <-s₁ (succ d) zero        ≡⟨ s₁→s₂ (succ d) zero ⟩
    <-s₂ (succ d) zero        ≡⟨ s₂→s₃ (succ d) zero ⟩
    <-s₃ (succ d) zero        ≡⟨ s₃→s₄ (succ d) zero ⟩
    <-s₄ (succ d) zero        ≡⟨ s₄→s₅ (succ d) zero ⟩
    <-s₅ (succ d) zero        ≡⟨ s₅→s₆ (succ d) zero ⟩
    <-s₆ (succ d) zero        ≡⟨ s₆→s₇ (succ d) zero true cZ₁ ⟩
    <-s₇ (succ d) zero true   ≡⟨ s₇→end (succ d) zero ⟩
    false
  ∎

lt-SS : (d e : D) → lt (succ d) (succ e) ≡ lt d e
lt-SS d e =
  begin
    fix lth ∙ (succ d) ∙ (succ e) ≡⟨ initial→s₁ (succ d) (succ e) ⟩
    <-s₁ (succ d) (succ e)        ≡⟨ s₁→s₂ (succ d) (succ e) ⟩
    <-s₂ (succ d) (succ e)        ≡⟨ s₂→s₃ (succ d) (succ e) ⟩
    <-s₃ (succ d) (succ e)        ≡⟨ s₃→s₄ (succ d) (succ e) ⟩
    <-s₄ (succ d) (succ e)        ≡⟨ s₄→s₅ (succ d) (succ e) ⟩
    <-s₅ (succ d) (succ e)        ≡⟨ s₅→s₆ (succ d) (succ e) ⟩
    <-s₆ (succ d) (succ e)        ≡⟨ s₆→s₇ (succ d) (succ e) false (cZ₂ e) ⟩
    <-s₇ (succ d) (succ e) false  ≡⟨ s₇→s₈ (succ d) (succ e) ⟩
    <-s₈ (succ d) (succ e)        ≡⟨ s₈→s₉ (succ d) (succ e) false (cZ₂ d) ⟩
    <-s₉ (succ d) (succ e) false  ≡⟨ s₉→s₁₀ (succ d) (succ e) ⟩
    <-s₁₀ (succ d) (succ e)       ≡⟨ s₁₀→s₁₁ d (succ e) ⟩
    <-s₁₁ d (succ e)              ≡⟨ s₁₁→s₁₂ d e ⟩
    <-s₁₂ d e                     ≡⟨ refl ⟩
    lt d e
  ∎

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
               (minus-0S Nn)
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
               (minus-SS Nm Nn)
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
                                           (minus-SS Nm Nn)
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
                                        (minus-SS Nm Nn)
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
                                        (minus-SS Nn Nm)
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
               (minus-SS Nm Nn)
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
