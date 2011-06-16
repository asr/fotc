------------------------------------------------------------------------------
-- Equations for the greatest common divisor
------------------------------------------------------------------------------

module FOTC.Program.GCD.Partial.EquationsI where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities

open import FOTC.Program.GCD.Partial.GCD

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------
private
  -- Before to prove some properties for 'gcd i j' it is convenient
  -- to descompose the behavior of the function step by step.

  -- Initially, we define the possible states (gcd-s₁,
  -- gcd-s₂, ...). Then we write down the proof for
  -- the execution step from the state p to the state q
  -- (e.g proof₂₋₃ : ∀ m n → gcd-s₂ m n → gcd-s₃ m n).

  -- The functions gcd-00, gcd-S0, gcd-0S, gcd-Sm>Sn and gcd-Sm≯Sn
  -- show the use of the states gcd-s₁, gcd-s₂, ..., and the proofs
  -- associated with the execution steps.

  ----------------------------------------------------------------------------
  -- The steps

  -- Initially, the equation gcd-eq is used.
  gcd-s₁ : D → D → D
  gcd-s₁ m n = if (isZero n)
                  then (if (isZero m)
                           then loop
                           else m)
                  else (if (isZero m)
                           then n
                           else (if (m > n)
                                    then gcd (m ∸ n) n
                                    else gcd m (n ∸ m)))

  -- First if_then_else (isZero n).
  gcd-s₂ : D → D → D → D
  gcd-s₂ m n b = if b
                    then (if (isZero m)
                             then loop
                             else m)
                    else (if (isZero m)
                             then n
                             else (if (m > n)
                                      then gcd (m ∸ n) n
                                      else gcd m (n ∸ m)))

  -- First if_then_else when isZero n = true.
  gcd-s₃ : D → D
  gcd-s₃ m  = if (isZero m) then loop else m

  -- First if_then_else when isZero n = false.
  gcd-s₄ : D → D → D
  gcd-s₄ m n = if (isZero m)
                  then n
                  else (if (m > n)
                           then gcd (m ∸ n) n
                           else gcd m (n ∸ m))

  -- Second if_then_else (isZero m).
  gcd-s₅ : D → D → D
  gcd-s₅ m b = if b then loop else m

  -- Second if_then_else when isZero m = true.
  gcd-s₆ : D
  gcd-s₆ = loop

  -- Second if_then_else when isZero m = false.
  gcd-s₇ : D → D
  gcd-s₇ m = m

  -- Third if_then_else (isZero m).
  gcd-s₈ : D → D → D → D
  gcd-s₈ m n b = if b
                    then n
                    else (if (m > n)
                             then gcd (m ∸ n) n
                             else gcd m (n ∸ m))

  -- Third if_then_else, when isZero m = true.
  gcd-s₉ : D → D
  gcd-s₉ n = n

  -- Third if_then_else, when isZero m = false.
  gcd-s₁₀ : D → D → D
  gcd-s₁₀ m n = if (m > n)
                   then gcd (m ∸ n) n
                   else gcd m (n ∸ m)

  -- Fourth if_then_else (gt m n).
  gcd-s₁₁ : D → D → D → D
  gcd-s₁₁ m n b = if b
                     then gcd (m ∸ n) n
                     else gcd m (n ∸ m)

  -- Fourth if_then_else when gt m n = true.
  gcd-s₁₂ : D → D → D
  gcd-s₁₂ m n = gcd (m ∸ n) n

  -- Fourth if_then_else when gt m n = false.
  gcd-s₁₃ : D → D → D
  gcd-s₁₃ m n = gcd m (n ∸ m)

  ----------------------------------------------------------------------------
  -- The execution steps

  {-
  To prove the execution steps
  (e.g. proof₃₋₄ : ∀ m n → gcd-s₃ m n → gcd_s₄ m n),
  we usually need to prove that

                         C [m] ≡ C [n] (1)

  given that
                             m ≡ n,    (2)

  where (2) is a conversion rule usually.
  We prove (1) using

  subst : ∀ {x y} (D : A → Set) → x ≡ y → P x → P y

  where
   P is given by λ m → C [m ] ≡ C [n],
   x ≡ y is given n ≡ m (actually, we use sym (m ≡ n)), and
   P x is given by C [n] ≡ C [n] (i.e. refl).
  -}

  proof₀₋₁ : ∀ m n → gcd m n ≡ gcd-s₁ m n
  proof₀₋₁ m n = gcd-eq m n

  proof₁₋₂ : ∀ m n b → isZero n ≡ b → gcd-s₁ m n ≡ gcd-s₂ m n b
  proof₁₋₂ m n b h = subst (λ x → gcd-s₂ m n x ≡ gcd-s₂ m n b)
                           (sym h)
                           refl

  proof₂₋₃ : ∀ m n → gcd-s₂ m n true ≡ gcd-s₃ m
  proof₂₋₃ m _ = if-true (gcd-s₃ m)

  proof₂₋₄ : ∀ m n → gcd-s₂ m n false ≡ gcd-s₄ m n
  proof₂₋₄ m n = if-false (gcd-s₄ m n)

  proof₃₋₅ : ∀ m b → isZero m ≡ b → gcd-s₃ m ≡ gcd-s₅ m b
  proof₃₋₅ m b h = subst (λ x → gcd-s₅ m x ≡ gcd-s₅ m b)
                         (sym h)
                         refl

  proof₅₋₆ : ∀ m → gcd-s₅ m true ≡ gcd-s₆
  proof₅₋₆ _ = if-true loop

  proof₅₋₇ : ∀ m → gcd-s₅ m false ≡ gcd-s₇ m
  proof₅₋₇ m = if-false m

  proof₄₋₈ : ∀ m n b → isZero m ≡ b → gcd-s₄ m n ≡ gcd-s₈ m n b
  proof₄₋₈ m n b h = subst (λ x → gcd-s₈ m n x ≡ gcd-s₈ m n b)
                           (sym h)
                           refl
  proof₈₋₉ : ∀ m n → gcd-s₈ m n true ≡ gcd-s₉ n
  proof₈₋₉ _ n = if-true n

  proof₈₋₁₀ : ∀ m n → gcd-s₈ m n false ≡ gcd-s₁₀ m n
  proof₈₋₁₀ m n = if-false (gcd-s₁₀ m n)

  proof₁₀₋₁₁ : ∀ m n b → m > n ≡ b → gcd-s₁₀ m n ≡ gcd-s₁₁ m n b
  proof₁₀₋₁₁ m n b h = subst (λ x → gcd-s₁₁ m n x ≡ gcd-s₁₁ m n b)
                             (sym h)
                             refl

  proof₁₁₋₁₂ : ∀ m n → gcd-s₁₁ m n true ≡ gcd-s₁₂ m n
  proof₁₁₋₁₂ m n = if-true (gcd (m ∸ n) n)

  proof₁₁₋₁₃ : ∀ m n → gcd-s₁₁ m n false ≡ gcd-s₁₃ m n
  proof₁₁₋₁₃ m n = if-false (gcd m (n ∸ m))

------------------------------------------------------------------------------
-- The five equations for gcd

-- First equation.
-- We do not use this equation for reasoning about gcd.
gcd-00 : gcd zero zero ≡ loop
gcd-00 =
  begin
    gcd zero zero         ≡⟨ proof₀₋₁ zero zero ⟩
    gcd-s₁ zero zero      ≡⟨ proof₁₋₂ zero zero true isZero-0 ⟩
    gcd-s₂ zero zero true ≡⟨ proof₂₋₃ zero zero ⟩
    gcd-s₃ zero           ≡⟨ proof₃₋₅ zero true isZero-0 ⟩
    gcd-s₅ zero true      ≡⟨ proof₅₋₆ zero ⟩
    loop
  ∎

-- Second equation.
gcd-S0 : ∀ n → gcd (succ n) zero ≡ succ n
gcd-S0 n =
  begin
    gcd (succ n) zero         ≡⟨ proof₀₋₁ (succ n) zero ⟩
    gcd-s₁ (succ n) zero      ≡⟨ proof₁₋₂ (succ n) zero true isZero-0 ⟩
    gcd-s₂ (succ n) zero true ≡⟨ proof₂₋₃ (succ n) zero ⟩
    gcd-s₃ (succ n)           ≡⟨ proof₃₋₅ (succ n) false (isZero-S n) ⟩
    gcd-s₅ (succ n) false     ≡⟨ proof₅₋₇ (succ n) ⟩
    succ n
  ∎

-- Third equation.
gcd-0S : ∀ n → gcd zero (succ n) ≡ succ n
gcd-0S n =
  begin
    gcd zero (succ n)          ≡⟨ proof₀₋₁ zero (succ n) ⟩
    gcd-s₁ zero (succ n)       ≡⟨ proof₁₋₂ zero (succ n) false (isZero-S n) ⟩
    gcd-s₂ zero (succ n) false ≡⟨ proof₂₋₄ zero (succ n) ⟩
    gcd-s₄ zero (succ n)       ≡⟨ proof₄₋₈ zero (succ n) true isZero-0 ⟩
    gcd-s₈ zero (succ n) true  ≡⟨ proof₈₋₉  zero (succ n) ⟩
    succ n
  ∎

-- Fourth equation.
gcd-S>S : ∀ m n → GT (succ m) (succ n) →
          gcd (succ m) (succ n) ≡ gcd (succ m ∸ succ n) (succ n)

gcd-S>S m n Sm>Sn =
  begin
    gcd (succ m) (succ n)          ≡⟨ proof₀₋₁ (succ m) (succ n) ⟩
    gcd-s₁ (succ m) (succ n)       ≡⟨ proof₁₋₂ (succ m) (succ n)
                                               false (isZero-S n)
                                   ⟩
    gcd-s₂ (succ m) (succ n) false ≡⟨ proof₂₋₄ (succ m) (succ n) ⟩
    gcd-s₄ (succ m) (succ n)       ≡⟨ proof₄₋₈ (succ m) (succ n)
                                               false (isZero-S m)
                                   ⟩
    gcd-s₈ (succ m) (succ n) false ≡⟨ proof₈₋₁₀ (succ m) (succ n) ⟩
    gcd-s₁₀ (succ m) (succ n)      ≡⟨ proof₁₀₋₁₁ (succ m) (succ n) true Sm>Sn ⟩
    gcd-s₁₁ (succ m) (succ n) true ≡⟨ proof₁₁₋₁₂ (succ m) (succ n) ⟩
    gcd (succ m ∸ succ n) (succ n)
  ∎

-- Fifth equation.
gcd-S≯S : ∀ m n → NGT (succ m) (succ n) →
          gcd (succ m) (succ n) ≡ gcd (succ m) (succ n ∸ succ m)
gcd-S≯S m n Sm≯Sn =
  begin
    gcd (succ m) (succ n)           ≡⟨ proof₀₋₁ (succ m) (succ n) ⟩
    gcd-s₁ (succ m) (succ n)        ≡⟨ proof₁₋₂ (succ m) (succ n)
                                                false (isZero-S n)
                                    ⟩
    gcd-s₂ (succ m) (succ n) false  ≡⟨ proof₂₋₄ (succ m) (succ n) ⟩
    gcd-s₄ (succ m) (succ n)        ≡⟨ proof₄₋₈ (succ m) (succ n)
                                                false (isZero-S m)
                                    ⟩
    gcd-s₈ (succ m) (succ n) false  ≡⟨ proof₈₋₁₀ (succ m) (succ n) ⟩
    gcd-s₁₀ (succ m) (succ n)       ≡⟨ proof₁₀₋₁₁ (succ m) (succ n)
                                                  false
                                                  Sm≯Sn
                                    ⟩
    gcd-s₁₁ (succ m) (succ n) false ≡⟨ proof₁₁₋₁₃ (succ m) (succ n) ⟩
    gcd (succ m) (succ n ∸ succ m)
  ∎
