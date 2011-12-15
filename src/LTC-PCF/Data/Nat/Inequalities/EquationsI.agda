------------------------------------------------------------------------------
-- Equations for the inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.Inequalities.EquationsI where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

private

  -- Before to prove some properties for 'lt i j' it is convenient
  -- to descompose the behavior of the function step by step.

  -- Initially, we define the possible states (<-s₁,
  -- <-s₂, ...). Then we write down the proof for
  -- the execution step from the state p to the state q
  --
  -- (e.g. s₁→s₂ : ∀ m n → <-s₂ m n → <-s₃ m n).

  -- The terms lt-00, lt-0S, lt-S0, and lt-S>S show the use of the
  -- states <-s₁, <-s₂, ..., and the proofs associated with the
  -- execution steps.

  ----------------------------------------------------------------------
  -- The steps of lt

  -- The conversion rule fix-f is applied.
  <-s₁ : D → D → D
  <-s₁ d e = <-h (fix <-h) · d · e

  -- Definition of <-h.
  <-s₂ : D → D → D
  <-s₂ d e = lam (<-helper₂ (fix <-h)) · d · e

  -- Beta application.
  <-s₃ : D → D → D
  <-s₃ d e = <-helper₂ (fix <-h) d · e

  -- Definition of lt-helper₂.
  <-s₄ : D → D → D
  <-s₄ d e = lam (<-helper₁ d (fix <-h)) · e

  -- Beta application.
  <-s₅ : D → D → D
  <-s₅ d e = <-helper₁ d (fix <-h) e

  -- Definition lt-helper₁.
  <-s₆ : D → D → D
  <-s₆ d e = if (iszero₁ e) then false
                else (if (iszero₁ d) then true
                         else ((fix <-h) · (pred₁ d) · (pred₁ e)))

  -- Reduction 'iszero₁ e ≡ b'.
  <-s₇ : D → D → D → D
  <-s₇ d e b = if b then false
                  else (if (iszero₁ d) then true
                           else ((fix <-h) · (pred₁ d) · (pred₁ e)))

  -- Reduction 'iszero₁ e ≡ false'.
  <-s₈ : D → D → D
  <-s₈ d e = if (iszero₁ d) then true
                 else ((fix <-h) · (pred₁ d) · (pred₁ e))

  -- Reduction 'iszero₁ d ≡ b'.
  <-s₉ : D → D → D → D
  <-s₉ d e b = if b then true
                  else ((fix <-h) · (pred₁ d) · (pred₁ e))

  -- Reduction 'iszero₁ d ≡ false'.
  <-s₁₀ : D → D → D
  <-s₁₀ d e = (fix <-h) · (pred₁ d) · (pred₁ e)

  -- Reduction 'pred₁ (succ d) ≡ d'.
  <-s₁₁ : D → D → D
  <-s₁₁ d e = (fix <-h) · d · (pred₁ e)

  -- Reduction 'pred₁ (succ e) ≡ e'.
  <-s₁₂ : D → D → D
  <-s₁₂ d e = (fix <-h) · d · e

  ----------------------------------------------------------------------
  -- The execution steps

  {-
    To prove the execution steps (e.g. s₃→s₄ : ∀ m n → <-s₃ m n → <-s₄ m n),
    we usually need to prove that

                         C [m] ≡ C [n]    (1)

    given that
                             m ≡ n,       (2)

    where (2) is a conversion rule usually.

    We prove (1) using

    subst : ∀ {x y} (P : D → Set) → x ≡ y → P x → P y

    where
      - P is given by λ t → C [m] ≡ C [t],
      - x ≡ y is given m ≡ n, and
      - P x is given by C [m] ≡ C [m] (i.e. refl).
  -}

  -- Application of the conversion rule fix₁-f.
  initial→s₁ : ∀ d e → fix <-h · d · e ≡ <-s₁ d e
  initial→s₁ d e = subst (λ t → fix <-h · d · e ≡ t · d · e) (fix-f <-h) refl

  -- The definition of <-h.
  s₁→s₂ : ∀ d e → <-s₁ d e ≡ <-s₂ d e
  s₁→s₂ d e = subst (λ t → <-h (fix <-h) · d · e ≡ t · d · e)
                    (<-h-≡ (fix <-h))
                    refl

  -- Beta application.
  s₂→s₃ : ∀ d e → <-s₂ d e ≡ <-s₃ d e
  s₂→s₃ d e = subst (λ t → lam (<-helper₂ (fix <-h)) · d · e ≡ t · e)
                    (beta (<-helper₂ (fix <-h)) d)
                    refl

  -- Definition of lt-helper₂
  s₃→s₄ : ∀ d e → <-s₃ d e ≡ <-s₄ d e
  s₃→s₄ d e = subst (λ t → <-helper₂ (fix <-h) d · e ≡ t · e)
                    (<-helper₂-≡ (fix <-h) d)
                    refl

  -- Beta application.
  s₄→s₅ : ∀ d e → <-s₄ d e ≡ <-s₅ d e
  s₄→s₅ d e = beta (<-helper₁ d (fix <-h)) e

  -- Definition of lt-helper₁.
  s₅→s₆ : ∀ d e → <-s₅ d e ≡ <-s₆ d e
  s₅→s₆ d e = <-helper₁-≡ d (fix <-h) e

  -- Reduction 'iszero₁ e ≡ b' using that proof.
  s₆→s₇ : ∀ d e b → iszero₁ e ≡ b → <-s₆ d e ≡ <-s₇ d e b
  s₆→s₇ d e b h = subst (λ t → <-s₆ d e ≡ <-s₇ d e t) h refl

  -- Reduction of 'iszero₁ e ≡ true' using the conversion rule if-true.
  s₇→end : ∀ d e → <-s₇ d e true ≡ false
  s₇→end _ _ = if-true false

  -- Reduction of 'iszero₁ e ≡ false ...' using the conversion rule if-false.
  s₇→s₈ : ∀ d e → <-s₇ d e false ≡ <-s₈ d e
  s₇→s₈ d e = if-false (<-s₈ d e)

  -- Reduction 'iszero₁ d ≡ b' using that proof.
  s₈→s₉ : ∀ d e b → iszero₁ d ≡ b → <-s₈ d e ≡ <-s₉ d e b
  s₈→s₉ d e b h = subst (λ t → <-s₈ d e ≡ <-s₉ d e t) h refl

  -- Reduction of 'iszero₁ d ≡ true' using the conversion rule if-true.
  s₉→end : ∀ d e → <-s₉ d e true ≡ true
  s₉→end _ _ = if-true true

  -- Reduction of 'iszero₁ d ≡ false ...' using the conversion rule if-false.
  s₉→s₁₀ : ∀ d e → <-s₉ d e false ≡ <-s₁₀ d e
  s₉→s₁₀ d e = if-false (<-s₁₀ d e)

  -- Reduction 'pred₁ (succ d) ≡ d' using the conversion rule pred₁-S.
  s₁₀→s₁₁ : ∀ d e → <-s₁₀ (succ₁ d) e ≡ <-s₁₁ d e
  s₁₀→s₁₁ d e = subst (λ t → <-s₁₀ (succ₁ d) e ≡ <-s₁₁ t e) (pred-S d) refl

  -- Reduction 'pred₁ (succ₁ e) ≡ e' using the conversion rule pred₁-S.
  s₁₁→s₁₂ : ∀ d e → <-s₁₁ d (succ₁ e) ≡ <-s₁₂ d e
  s₁₁→s₁₂ d e = subst (λ t → <-s₁₁ d (succ₁ e) ≡ <-s₁₂ d t) (pred-S e) refl

------------------------------------------------------------------------------

<-00 : NLT zero zero
<-00 =
  begin
    fix <-h · zero · zero ≡⟨ initial→s₁ zero zero ⟩
    <-s₁ zero zero         ≡⟨ s₁→s₂ zero zero ⟩
    <-s₂ zero zero         ≡⟨ s₂→s₃ zero zero ⟩
    <-s₃ zero zero         ≡⟨ s₃→s₄ zero zero ⟩
    <-s₄ zero zero         ≡⟨ s₄→s₅ zero zero ⟩
    <-s₅ zero zero         ≡⟨ s₅→s₆ zero zero ⟩
    <-s₆ zero zero         ≡⟨ s₆→s₇ zero zero true iszero-0 ⟩
    <-s₇ zero zero true    ≡⟨ s₇→end zero zero ⟩
    false
    ∎

<-0S : ∀ d → LT zero (succ₁ d)
<-0S d =
  begin
    fix <-h · zero · (succ₁ d) ≡⟨ initial→s₁ zero (succ₁ d) ⟩
    <-s₁ zero (succ₁ d)         ≡⟨ s₁→s₂ zero (succ₁ d) ⟩
    <-s₂ zero (succ₁ d)         ≡⟨ s₂→s₃ zero (succ₁ d) ⟩
    <-s₃ zero (succ₁ d)         ≡⟨ s₃→s₄ zero (succ₁ d) ⟩
    <-s₄ zero (succ₁ d)         ≡⟨ s₄→s₅ zero (succ₁ d) ⟩
    <-s₅ zero (succ₁ d)         ≡⟨ s₅→s₆ zero (succ₁ d) ⟩
    <-s₆ zero (succ₁ d)         ≡⟨ s₆→s₇ zero (succ₁ d) false (iszero-S d) ⟩
    <-s₇ zero (succ₁ d) false   ≡⟨ s₇→s₈ zero (succ₁ d) ⟩
    <-s₈ zero (succ₁ d)         ≡⟨ s₈→s₉ zero (succ₁ d) true iszero-0 ⟩
    <-s₉ zero (succ₁ d) true    ≡⟨ s₉→end zero (succ₁ d) ⟩
    true
  ∎

<-S0 : ∀ d → NLT (succ₁ d) zero
<-S0 d =
  begin
    fix <-h · (succ₁ d) · zero ≡⟨ initial→s₁ (succ₁ d) zero ⟩
    <-s₁ (succ₁ d) zero         ≡⟨ s₁→s₂ (succ₁ d) zero ⟩
    <-s₂ (succ₁ d) zero         ≡⟨ s₂→s₃ (succ₁ d) zero ⟩
    <-s₃ (succ₁ d) zero         ≡⟨ s₃→s₄ (succ₁ d) zero ⟩
    <-s₄ (succ₁ d) zero         ≡⟨ s₄→s₅ (succ₁ d) zero ⟩
    <-s₅ (succ₁ d) zero         ≡⟨ s₅→s₆ (succ₁ d) zero ⟩
    <-s₆ (succ₁ d) zero         ≡⟨ s₆→s₇ (succ₁ d) zero true iszero-0 ⟩
    <-s₇ (succ₁ d) zero true    ≡⟨ s₇→end (succ₁ d) zero ⟩
    false
  ∎

<-SS : ∀ d e → succ₁ d < succ₁ e ≡ d < e
<-SS d e =
  begin
    fix <-h · (succ₁ d) · (succ₁ e) ≡⟨ initial→s₁ (succ₁ d) (succ₁ e) ⟩
    <-s₁ (succ₁ d) (succ₁ e)         ≡⟨ s₁→s₂ (succ₁ d) (succ₁ e) ⟩
    <-s₂ (succ₁ d) (succ₁ e)         ≡⟨ s₂→s₃ (succ₁ d) (succ₁ e) ⟩
    <-s₃ (succ₁ d) (succ₁ e)         ≡⟨ s₃→s₄ (succ₁ d) (succ₁ e) ⟩
    <-s₄ (succ₁ d) (succ₁ e)         ≡⟨ s₄→s₅ (succ₁ d) (succ₁ e) ⟩
    <-s₅ (succ₁ d) (succ₁ e)         ≡⟨ s₅→s₆ (succ₁ d) (succ₁ e) ⟩
    <-s₆ (succ₁ d) (succ₁ e)         ≡⟨ s₆→s₇ (succ₁ d) (succ₁ e)
                                              false (iszero-S e)
                                     ⟩
    <-s₇ (succ₁ d) (succ₁ e) false   ≡⟨ s₇→s₈ (succ₁ d) (succ₁ e) ⟩
    <-s₈ (succ₁ d) (succ₁ e)         ≡⟨ s₈→s₉ (succ₁ d) (succ₁ e)
                                              false (iszero-S d)
                                     ⟩
    <-s₉ (succ₁ d) (succ₁ e) false   ≡⟨ s₉→s₁₀ (succ₁ d) (succ₁ e) ⟩
    <-s₁₀ (succ₁ d) (succ₁ e)        ≡⟨ s₁₀→s₁₁ d (succ₁ e) ⟩
    <-s₁₁ d (succ₁ e)                ≡⟨ s₁₁→s₁₂ d e ⟩
    <-s₁₂ d e                        ≡⟨ refl ⟩
    d < e
  ∎
