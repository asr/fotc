------------------------------------------------------------------------------
-- Conversion rules for the greatest common divisor
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.GCD.Partial.ConversionRulesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.Loop
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Program.GCD.Partial.GCD

------------------------------------------------------------------------------
private
  -- Before to prove some properties for the gcd it is convenient to
  -- descompose the behavior of the function step by step.

  -- Initially, we define the possible states (gcd-s₁, gcd-s₂,
  -- ...). Then we write down the proof for the execution step from
  -- the state p to the state q, e.g.

  -- proof₂₋₃ : ∀ m n → gcd-s₂ m n → gcd-s₃ m n.

  -- The functions gcd-00, gcd-S0, gcd-0S, gcd-Sm>Sn, and gcd-Sm≯Sn
  -- show the use of the states gcd-s₁, gcd-s₂, ..., and the proofs
  -- associated with the execution steps.

  ----------------------------------------------------------------------------
  -- The steps

  -- Initially, the equation gcd-eq is used.
  gcd-s₁ : D → D → D
  gcd-s₁ m n = if (iszero₁ n)
                  then (if (iszero₁ m)
                          then error
                          else m)
                  else (if (iszero₁ m)
                          then n
                          else (if (gt m n)
                                  then gcd (m ∸ n) n
                                  else gcd m (n ∸ m)))

  -- First if_then_else_ (iszero₁ n).
  gcd-s₂ : D → D → D → D
  gcd-s₂ m n b = if b
                    then (if (iszero₁ m)
                            then error
                            else m)
                    else (if (iszero₁ m)
                            then n
                            else (if (gt m n)
                                    then gcd (m ∸ n) n
                                    else gcd m (n ∸ m)))

  -- First if_then_else_ when iszero₁ n = true.
  gcd-s₃ : D → D
  gcd-s₃ m = if (iszero₁ m) then error else m

  -- First if_then_else_ when iszero₁ n = false.
  gcd-s₄ : D → D → D
  gcd-s₄ m n = if (iszero₁ m)
                 then n
                 else (if (gt m  n) then gcd (m ∸ n) n else gcd m (n ∸ m))

  -- Second if_then_else_ (iszero₁ m).
  gcd-s₅ : D → D → D
  gcd-s₅ m b = if b then error else m

  -- Second if_then_else_ when iszero₁ m = true.
  gcd-s₆ : D
  gcd-s₆ = error

  -- Second if_then_else_ when iszero₁ m = false.
  gcd-s₇ : D → D
  gcd-s₇ m = m

  -- Third if_then_else_ (iszero₁ m).
  gcd-s₈ : D → D → D → D
  gcd-s₈ m n b = if b
                   then n
                   else (if (gt m n) then gcd (m ∸ n) n else gcd m (n ∸ m))

  -- Third if_then_else_, when iszero₁ m = true.
  gcd-s₉ : D → D
  gcd-s₉ n = n

  -- Third if_then_else_, when iszero₁ m = false.
  gcd-s₁₀ : D → D → D
  gcd-s₁₀ m n = if (gt m n) then gcd (m ∸ n) n else gcd m (n ∸ m)

  -- Fourth if_then_else_ (gt m n).
  gcd-s₁₁ : D → D → D → D
  gcd-s₁₁ m n b = if b then gcd (m ∸ n) n else gcd m (n ∸ m)

  -- Fourth if_then_else_ when gt m n = true.
  gcd-s₁₂ : D → D → D
  gcd-s₁₂ m n = gcd (m ∸ n) n

  -- Fourth if_then_else_ when gt m n = false.
  gcd-s₁₃ : D → D → D
  gcd-s₁₃ m n = gcd m (n ∸ m)

  ----------------------------------------------------------------------------
  -- The execution steps

  {-

  To prove the execution steps, e.g.

  proof₃₋₄ : ∀ m n → gcd-s₃ m n → gcd_s₄ m n,

  we usually need to prove that

                         C [m] ≡ C [n] (1)

  given that
                             m ≡ n,    (2)

  where (2) is a conversion rule usually.
  We prove (1) using

  subst : ∀ {x y} (D : A → Set) → x ≡ y → P x → P y

  where
   • P is given by λ m → C [m ] ≡ C [n],
   • x ≡ y is given n ≡ m (actually, we use sym (m ≡ n)), and
   • P x is given by C [n] ≡ C [n] (i.e. refl).
  -}

  proof₀₋₁ : ∀ m n → gcd m n ≡ gcd-s₁ m n
  proof₀₋₁ = gcd-eq

  proof₁₋₂ : ∀ m n b → iszero₁ n ≡ b → gcd-s₁ m n ≡ gcd-s₂ m n b
  proof₁₋₂ m n .(iszero₁ n) refl = refl

  proof₂₋₃ : ∀ m n → gcd-s₂ m n true ≡ gcd-s₃ m
  proof₂₋₃ m _ = if-true (gcd-s₃ m)

  proof₂₋₄ : ∀ m n → gcd-s₂ m n false ≡ gcd-s₄ m n
  proof₂₋₄ m n = if-false (gcd-s₄ m n)

  proof₃₋₅ : ∀ m b → iszero₁ m ≡ b → gcd-s₃ m ≡ gcd-s₅ m b
  proof₃₋₅ m .(iszero₁ m) refl = refl

  proof₅₋₆ : ∀ m → gcd-s₅ m true ≡ gcd-s₆
  proof₅₋₆ _ = if-true error

  proof₅₋₇ : ∀ m → gcd-s₅ m false ≡ gcd-s₇ m
  proof₅₋₇ m = if-false m

  proof₄₋₈ : ∀ m n b → iszero₁ m ≡ b → gcd-s₄ m n ≡ gcd-s₈ m n b
  proof₄₋₈ m n .(iszero₁ m) refl = refl

  proof₈₋₉ : ∀ m n → gcd-s₈ m n true ≡ gcd-s₉ n
  proof₈₋₉ _ n = if-true n

  proof₈₋₁₀ : ∀ m n → gcd-s₈ m n false ≡ gcd-s₁₀ m n
  proof₈₋₁₀ m n = if-false (gcd-s₁₀ m n)

  proof₁₀₋₁₁ : ∀ m n b → gt m n ≡ b → gcd-s₁₀ m n ≡ gcd-s₁₁ m n b
  proof₁₀₋₁₁ m n .(lt n m) refl = refl

  proof₁₁₋₁₂ : ∀ m n → gcd-s₁₁ m n true ≡ gcd-s₁₂ m n
  proof₁₁₋₁₂ m n = if-true (gcd (m ∸ n) n)

  proof₁₁₋₁₃ : ∀ m n → gcd-s₁₁ m n false ≡ gcd-s₁₃ m n
  proof₁₁₋₁₃ m n = if-false (gcd m (n ∸ m))

------------------------------------------------------------------------------
-- The five equations for gcd

-- First equation.
-- We do not use this equation for reasoning about gcd.
gcd-00 : gcd zero zero ≡ error
gcd-00 =
  gcd zero zero         ≡⟨ proof₀₋₁ zero zero ⟩
  gcd-s₁ zero zero      ≡⟨ proof₁₋₂ zero zero true iszero-0 ⟩
  gcd-s₂ zero zero true ≡⟨ proof₂₋₃ zero zero ⟩
  gcd-s₃ zero           ≡⟨ proof₃₋₅ zero true iszero-0 ⟩
  gcd-s₅ zero true      ≡⟨ proof₅₋₆ zero ⟩
  error                 ∎

-- Second equation.
gcd-S0 : ∀ n → gcd (succ₁ n) zero ≡ succ₁ n
gcd-S0 n =
  gcd (succ₁ n) zero         ≡⟨ proof₀₋₁ (succ₁ n) zero ⟩
  gcd-s₁ (succ₁ n) zero      ≡⟨ proof₁₋₂ (succ₁ n) zero true iszero-0 ⟩
  gcd-s₂ (succ₁ n) zero true ≡⟨ proof₂₋₃ (succ₁ n) zero ⟩
  gcd-s₃ (succ₁ n)           ≡⟨ proof₃₋₅ (succ₁ n) false (iszero-S n) ⟩
  gcd-s₅ (succ₁ n) false     ≡⟨ proof₅₋₇ (succ₁ n) ⟩
  succ₁ n                    ∎

-- Third equation.
gcd-0S : ∀ n → gcd zero (succ₁ n) ≡ succ₁ n
gcd-0S n =
  gcd zero (succ₁ n)          ≡⟨ proof₀₋₁ zero (succ₁ n) ⟩
  gcd-s₁ zero (succ₁ n)       ≡⟨ proof₁₋₂ zero (succ₁ n) false (iszero-S n) ⟩
  gcd-s₂ zero (succ₁ n) false ≡⟨ proof₂₋₄ zero (succ₁ n) ⟩
  gcd-s₄ zero (succ₁ n)       ≡⟨ proof₄₋₈ zero (succ₁ n) true iszero-0 ⟩
  gcd-s₈ zero (succ₁ n) true  ≡⟨ proof₈₋₉  zero (succ₁ n) ⟩
  succ₁ n                     ∎

-- Fourth equation.
gcd-S>S : ∀ m n → succ₁ m > succ₁ n →
          gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m ∸ succ₁ n) (succ₁ n)

gcd-S>S m n Sm>Sn =
  gcd (succ₁ m) (succ₁ n)           ≡⟨ proof₀₋₁ (succ₁ m) (succ₁ n) ⟩
  gcd-s₁ (succ₁ m) (succ₁ n)        ≡⟨ proof₁₋₂ (succ₁ m) (succ₁ n) false (iszero-S n) ⟩
  gcd-s₂ (succ₁ m) (succ₁ n) false  ≡⟨ proof₂₋₄ (succ₁ m) (succ₁ n) ⟩
  gcd-s₄ (succ₁ m) (succ₁ n)        ≡⟨ proof₄₋₈ (succ₁ m) (succ₁ n) false (iszero-S m) ⟩
  gcd-s₈ (succ₁ m) (succ₁ n) false  ≡⟨ proof₈₋₁₀ (succ₁ m) (succ₁ n) ⟩
  gcd-s₁₀ (succ₁ m) (succ₁ n)       ≡⟨ proof₁₀₋₁₁ (succ₁ m) (succ₁ n) true Sm>Sn ⟩
  gcd-s₁₁ (succ₁ m) (succ₁ n) true  ≡⟨ proof₁₁₋₁₂ (succ₁ m) (succ₁ n) ⟩
  gcd (succ₁ m ∸ succ₁ n) (succ₁ n) ∎

-- Fifth equation.
gcd-S≯S : ∀ m n → succ₁ m ≯ succ₁ n →
          gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m) (succ₁ n ∸ succ₁ m)
gcd-S≯S m n Sm≯Sn =
  gcd (succ₁ m) (succ₁ n)           ≡⟨ proof₀₋₁ (succ₁ m) (succ₁ n) ⟩
  gcd-s₁ (succ₁ m) (succ₁ n)        ≡⟨ proof₁₋₂ (succ₁ m) (succ₁ n) false (iszero-S n) ⟩
  gcd-s₂ (succ₁ m) (succ₁ n) false  ≡⟨ proof₂₋₄ (succ₁ m) (succ₁ n) ⟩
  gcd-s₄ (succ₁ m) (succ₁ n)        ≡⟨ proof₄₋₈ (succ₁ m) (succ₁ n) false (iszero-S m) ⟩
  gcd-s₈ (succ₁ m) (succ₁ n) false  ≡⟨ proof₈₋₁₀ (succ₁ m) (succ₁ n) ⟩
  gcd-s₁₀ (succ₁ m) (succ₁ n)       ≡⟨ proof₁₀₋₁₁ (succ₁ m) (succ₁ n) false Sm≯Sn ⟩
  gcd-s₁₁ (succ₁ m) (succ₁ n) false ≡⟨ proof₁₁₋₁₃ (succ₁ m) (succ₁ n) ⟩
  gcd (succ₁ m) (succ₁ n ∸ succ₁ m) ∎
