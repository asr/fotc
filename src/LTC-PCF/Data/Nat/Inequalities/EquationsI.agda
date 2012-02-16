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
  <-s₁ m n = <-h (fix <-h) · m · n

  -- Definition of <-h.
  <-s₂ : D → D → D
  <-s₂ m n = lam (<-helper₂ (fix <-h)) · m · n

  -- Beta application.
  <-s₃ : D → D → D
  <-s₃ m n = <-helper₂ (fix <-h) m · n

  -- Definition of lt-helper₂.
  <-s₄ : D → D → D
  <-s₄ m n = lam (<-helper₁ m (fix <-h)) · n

  -- Beta application.
  <-s₅ : D → D → D
  <-s₅ m n = <-helper₁ m (fix <-h) n

  -- Definition lt-helper₁.
  <-s₆ : D → D → D
  <-s₆ m n = if (iszero₁ n) then false
                else (if (iszero₁ m) then true
                         else ((fix <-h) · (pred₁ m) · (pred₁ n)))

  -- Reduction 'iszero₁ n ≡ b'.
  <-s₇ : D → D → D → D
  <-s₇ m n b = if b then false
                  else (if (iszero₁ m) then true
                           else ((fix <-h) · (pred₁ m) · (pred₁ n)))

  -- Reduction 'iszero₁ n ≡ false'.
  <-s₈ : D → D → D
  <-s₈ m n = if (iszero₁ m) then true
                 else ((fix <-h) · (pred₁ m) · (pred₁ n))

  -- Reduction 'iszero₁ m ≡ b'.
  <-s₉ : D → D → D → D
  <-s₉ m n b = if b then true
                  else ((fix <-h) · (pred₁ m) · (pred₁ n))

  -- Reduction 'iszero₁ m ≡ false'.
  <-s₁₀ : D → D → D
  <-s₁₀ m n = (fix <-h) · (pred₁ m) · (pred₁ n)

  -- Reduction 'pred₁ (succ m) ≡ m'.
  <-s₁₁ : D → D → D
  <-s₁₁ m n = (fix <-h) · m · (pred₁ n)

  -- Reduction 'pred₁ (succ n) ≡ n'.
  <-s₁₂ : D → D → D
  <-s₁₂ m n = (fix <-h) · m · n

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
  initial→s₁ : ∀ m n → fix <-h · m · n ≡ <-s₁ m n
  initial→s₁ m n = subst (λ t → fix <-h · m · n ≡ t · m · n) (fix-f <-h) refl

  -- The definition of <-h.
  s₁→s₂ : ∀ m n → <-s₁ m n ≡ <-s₂ m n
  s₁→s₂ m n = subst (λ t → <-h (fix <-h) · m · n ≡ t · m · n)
                    (<-h-≡ (fix <-h))
                    refl

  -- Beta application.
  s₂→s₃ : ∀ m n → <-s₂ m n ≡ <-s₃ m n
  s₂→s₃ m n = subst (λ t → lam (<-helper₂ (fix <-h)) · m · n ≡ t · n)
                    (beta (<-helper₂ (fix <-h)) m)
                    refl

  -- Definition of lt-helper₂
  s₃→s₄ : ∀ m n → <-s₃ m n ≡ <-s₄ m n
  s₃→s₄ m n = subst (λ t → <-helper₂ (fix <-h) m · n ≡ t · n)
                    (<-helper₂-≡ (fix <-h) m)
                    refl

  -- Beta application.
  s₄→s₅ : ∀ m n → <-s₄ m n ≡ <-s₅ m n
  s₄→s₅ m n = beta (<-helper₁ m (fix <-h)) n

  -- Definition of lt-helper₁.
  s₅→s₆ : ∀ m n → <-s₅ m n ≡ <-s₆ m n
  s₅→s₆ m n = <-helper₁-≡ m (fix <-h) n

  -- Reduction 'iszero₁ n ≡ b' using that proof.
  s₆→s₇ : ∀ m n b → iszero₁ n ≡ b → <-s₆ m n ≡ <-s₇ m n b
  s₆→s₇ m n b h = subst (λ t → <-s₆ m n ≡ <-s₇ m n t) h refl

  -- Reduction of 'iszero₁ n ≡ true' using the conversion rule if-true.
  s₇→end : ∀ m n → <-s₇ m n true ≡ false
  s₇→end _ _ = if-true false

  -- Reduction of 'iszero₁ n ≡ false ...' using the conversion rule if-false.
  s₇→s₈ : ∀ m n → <-s₇ m n false ≡ <-s₈ m n
  s₇→s₈ m n = if-false (<-s₈ m n)

  -- Reduction 'iszero₁ m ≡ b' using that proof.
  s₈→s₉ : ∀ m n b → iszero₁ m ≡ b → <-s₈ m n ≡ <-s₉ m n b
  s₈→s₉ m n b h = subst (λ t → <-s₈ m n ≡ <-s₉ m n t) h refl

  -- Reduction of 'iszero₁ m ≡ true' using the conversion rule if-true.
  s₉→end : ∀ m n → <-s₉ m n true ≡ true
  s₉→end _ _ = if-true true

  -- Reduction of 'iszero₁ m ≡ false ...' using the conversion rule if-false.
  s₉→s₁₀ : ∀ m n → <-s₉ m n false ≡ <-s₁₀ m n
  s₉→s₁₀ m n = if-false (<-s₁₀ m n)

  -- Reduction 'pred₁ (succ m) ≡ m' using the conversion rule pred₁-S.
  s₁₀→s₁₁ : ∀ m n → <-s₁₀ (succ₁ m) n ≡ <-s₁₁ m n
  s₁₀→s₁₁ m n = subst (λ t → <-s₁₀ (succ₁ m) n ≡ <-s₁₁ t n) (pred-S m) refl

  -- Reduction 'pred₁ (succ₁ n) ≡ n' using the conversion rule pred₁-S.
  s₁₁→s₁₂ : ∀ m n → <-s₁₁ m (succ₁ n) ≡ <-s₁₂ m n
  s₁₁→s₁₂ m n = subst (λ t → <-s₁₁ m (succ₁ n) ≡ <-s₁₂ m t) (pred-S n) refl

------------------------------------------------------------------------------

<-00 : NLT zero zero
<-00 =
  fix <-h · zero · zero ≡⟨ initial→s₁ zero zero ⟩
  <-s₁ zero zero        ≡⟨ s₁→s₂ zero zero ⟩
  <-s₂ zero zero        ≡⟨ s₂→s₃ zero zero ⟩
  <-s₃ zero zero        ≡⟨ s₃→s₄ zero zero ⟩
  <-s₄ zero zero        ≡⟨ s₄→s₅ zero zero ⟩
  <-s₅ zero zero        ≡⟨ s₅→s₆ zero zero ⟩
  <-s₆ zero zero        ≡⟨ s₆→s₇ zero zero true iszero-0 ⟩
  <-s₇ zero zero true   ≡⟨ s₇→end zero zero ⟩
  false ∎

<-0S : ∀ n → LT zero (succ₁ n)
<-0S n =
  fix <-h · zero · (succ₁ n) ≡⟨ initial→s₁ zero (succ₁ n) ⟩
  <-s₁ zero (succ₁ n)        ≡⟨ s₁→s₂ zero (succ₁ n) ⟩
  <-s₂ zero (succ₁ n)        ≡⟨ s₂→s₃ zero (succ₁ n) ⟩
  <-s₃ zero (succ₁ n)        ≡⟨ s₃→s₄ zero (succ₁ n) ⟩
  <-s₄ zero (succ₁ n)        ≡⟨ s₄→s₅ zero (succ₁ n) ⟩
  <-s₅ zero (succ₁ n)        ≡⟨ s₅→s₆ zero (succ₁ n) ⟩
  <-s₆ zero (succ₁ n)        ≡⟨ s₆→s₇ zero (succ₁ n) false (iszero-S n) ⟩
  <-s₇ zero (succ₁ n) false  ≡⟨ s₇→s₈ zero (succ₁ n) ⟩
  <-s₈ zero (succ₁ n)        ≡⟨ s₈→s₉ zero (succ₁ n) true iszero-0 ⟩
  <-s₉ zero (succ₁ n) true   ≡⟨ s₉→end zero (succ₁ n) ⟩
  true ∎

<-S0 : ∀ n → NLT (succ₁ n) zero
<-S0 n =
  fix <-h · (succ₁ n) · zero ≡⟨ initial→s₁ (succ₁ n) zero ⟩
  <-s₁ (succ₁ n) zero        ≡⟨ s₁→s₂ (succ₁ n) zero ⟩
  <-s₂ (succ₁ n) zero        ≡⟨ s₂→s₃ (succ₁ n) zero ⟩
  <-s₃ (succ₁ n) zero        ≡⟨ s₃→s₄ (succ₁ n) zero ⟩
  <-s₄ (succ₁ n) zero        ≡⟨ s₄→s₅ (succ₁ n) zero ⟩
  <-s₅ (succ₁ n) zero        ≡⟨ s₅→s₆ (succ₁ n) zero ⟩
  <-s₆ (succ₁ n) zero        ≡⟨ s₆→s₇ (succ₁ n) zero true iszero-0 ⟩
  <-s₇ (succ₁ n) zero true   ≡⟨ s₇→end (succ₁ n) zero ⟩
  false ∎

<-SS : ∀ m n → succ₁ m < succ₁ n ≡ m < n
<-SS m n =
  fix <-h · (succ₁ m) · (succ₁ n) ≡⟨ initial→s₁ (succ₁ m) (succ₁ n) ⟩
  <-s₁ (succ₁ m) (succ₁ n)        ≡⟨ s₁→s₂ (succ₁ m) (succ₁ n) ⟩
  <-s₂ (succ₁ m) (succ₁ n)        ≡⟨ s₂→s₃ (succ₁ m) (succ₁ n) ⟩
  <-s₃ (succ₁ m) (succ₁ n)        ≡⟨ s₃→s₄ (succ₁ m) (succ₁ n) ⟩
  <-s₄ (succ₁ m) (succ₁ n)        ≡⟨ s₄→s₅ (succ₁ m) (succ₁ n) ⟩
  <-s₅ (succ₁ m) (succ₁ n)        ≡⟨ s₅→s₆ (succ₁ m) (succ₁ n) ⟩
  <-s₆ (succ₁ m) (succ₁ n)        ≡⟨ s₆→s₇ (succ₁ m) (succ₁ n) false (iszero-S n) ⟩
  <-s₇ (succ₁ m) (succ₁ n) false  ≡⟨ s₇→s₈ (succ₁ m) (succ₁ n) ⟩
  <-s₈ (succ₁ m) (succ₁ n)        ≡⟨ s₈→s₉ (succ₁ m) (succ₁ n) false (iszero-S m) ⟩
  <-s₉ (succ₁ m) (succ₁ n) false  ≡⟨ s₉→s₁₀ (succ₁ m) (succ₁ n) ⟩
  <-s₁₀ (succ₁ m) (succ₁ n)       ≡⟨ s₁₀→s₁₁ m (succ₁ n) ⟩
  <-s₁₁ m (succ₁ n)               ≡⟨ s₁₁→s₁₂ m n ⟩
  <-s₁₂ m n                       ≡⟨ refl ⟩
  m < n ∎
