------------------------------------------------------------------------------
-- Conversion rules for the greatest common divisor
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.LTC-PCF.Program.GCD.Total.ConversionRules where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.LTC-PCF.Base
open import Interactive.LTC-PCF.Data.Nat
open import Interactive.LTC-PCF.Data.Nat.Inequalities
open import Interactive.LTC-PCF.Data.Nat.Inequalities.Properties
open import Interactive.LTC-PCF.Program.GCD.Total.GCD

------------------------------------------------------------------------------

private
  -- Before to prove some properties for the gcd it is convenient to
  -- descompose the behavior of the function step by step.

  -- Initially, we define the possible states (gcd-s₁, gcd-s₂,
  -- ...). Then we write down the proof for the execution step from
  -- the state p to the state q, e.g.
  --
  -- proof₂₋₃ : ∀ m n → gcd-s₂ m n → gcd-s₃ m n.

  -- The functions gcd-00, gcd-S0, gcd-0S, gcd-Sm>Sn and gcd-Sm≯Sn
  -- show the use of the states gcd-s₁, gcd-s₂, ..., and the proofs
  -- associated with the execution steps.

  ----------------------------------------------------------------------------
  -- The steps

  -- Initially, the conversion rule fix-eq is applied.
  gcd-s₁ : D → D → D
  gcd-s₁ m n = gcdh (fix gcdh) · m · n

  -- First argument application.
  gcd-s₂ : D → D
  gcd-s₂ m = lam (λ n →
               if (iszero₁ n)
                 then m
                 else (if (iszero₁ m)
                         then n
                         else (if (gt m n)
                                 then fix gcdh · (m ∸ n) · n
                                 else fix gcdh · m · (n ∸ m))))

  -- Second argument application.
  gcd-s₃ : D → D → D
  gcd-s₃ m n = if (iszero₁ n)
                 then m
                 else (if (iszero₁ m)
                         then n
                         else (if (gt m n)
                                 then fix gcdh · (m ∸ n) · n
                                 else fix gcdh · m · (n ∸ m)))

  -- First if_then_else_ iszero₁ n = b.
  gcd-s₄ : D → D → D → D
  gcd-s₄ m n b = if b
                   then m
                   else (if (iszero₁ m)
                           then n
                           else (if (gt m n)
                                   then fix gcdh · (m ∸ n) · n
                                   else fix gcdh · m · (n ∸ m)))

  -- First if_then_else_ when if true ...
  gcd-s₅ : D → D
  gcd-s₅ m = m

  -- First if_then_else_ when if false ...
  gcd-s₆ : D → D → D
  gcd-s₆ m n = if (iszero₁ m)
                 then n
                 else (if (gt m n)
                         then fix gcdh · (m ∸ n) · n
                         else fix gcdh · m · (n ∸ m))

  -- Second if_then_else_ iszero₁ m = b.
  gcd-s₇ : D → D → D → D
  gcd-s₇ m n b = if b
                   then n
                   else (if (gt m n)
                           then fix gcdh · (m ∸ n) · n
                           else fix gcdh · m · (n ∸ m))

  -- Second if_then_else_ when if false ...
  gcd-s₈ : D → D → D
  gcd-s₈ m n = if (gt m n)
                  then fix gcdh · (m ∸ n) · n
                  else fix gcdh · m · (n ∸ m)

  -- Third if_then_else_ gt m n = b.
  gcd-s₉ : D → D → D → D
  gcd-s₉ m n b = if b then fix gcdh · (m ∸ n) · n else fix gcdh · m · (n ∸ m)

  ----------------------------------------------------------------------------
  -- Congruence properties

  gcd-s₉Cong₃ : ∀ {m n b b'} → b ≡ b' → gcd-s₉ m n b ≡ gcd-s₉ m n b'
  gcd-s₉Cong₃ refl = refl

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
   • x ≡ y is given n ≡ m (actually, we use sym (m ≡ n)) and
   • P x is given by C [n] ≡ C [n] (i.e. refl).
  -}

  proof₀₋₁ : ∀ m n → fix gcdh · m · n ≡ gcd-s₁ m n
  proof₀₋₁ m n = subst (λ x → x · m · n ≡ gcdh (fix gcdh) · m · n)
                       (sym (fix-eq gcdh))
                       refl

  proof₁₋₂ : ∀ m n → gcd-s₁ m n ≡ gcd-s₂ m · n
  proof₁₋₂ m n = subst (λ x → x · n ≡ gcd-s₂ m · n)
                       (sym (beta gcd-s₂ m))
                       refl

  proof₂₋₃ : ∀ m n → gcd-s₂ m · n ≡ gcd-s₃ m n
  proof₂₋₃ m n = beta (gcd-s₃ m) n

  -- 25 April 2014. Failed with Andreas' --without-K.
  proof₃₋₄ : ∀ m n b → iszero₁ n ≡ b → gcd-s₃ m n ≡ gcd-s₄ m n b
  proof₃₋₄ m n .(iszero₁ n) refl = refl

  proof₄₊ : ∀ m n → gcd-s₄ m n true ≡ gcd-s₅ m
  proof₄₊ m _ = if-true (gcd-s₅ m)

  proof₄₋₆ : ∀ m n → gcd-s₄ m n false ≡ gcd-s₆ m n
  proof₄₋₆ m n = if-false (gcd-s₆ m n)

  proof₆₋₇ : ∀ m n b → iszero₁ m ≡ b → gcd-s₆ m n ≡ gcd-s₇ m n b
  proof₆₋₇ m n .(iszero₁ m) refl = refl

  proof₇₊ : ∀ m n → gcd-s₇ m n true ≡ n
  proof₇₊ _ n = if-true n

  proof₇₋₈ : ∀ m n → gcd-s₇ m n false ≡ gcd-s₈ m n
  proof₇₋₈ m n = if-false (gcd-s₈ m n)

  proof₈₋₉ : ∀ m n b → gt m n ≡ b → gcd-s₈ m n ≡ gcd-s₉ m n b
  proof₈₋₉ m n b = gcd-s₉Cong₃

  proof₉₊ : ∀ m n → gcd-s₉ m n true ≡ fix gcdh · (m ∸ n) · n
  proof₉₊ m n = if-true (fix gcdh · (m ∸ n) · n)

  proof₉₋ : ∀ m n → gcd-s₉ m n false ≡ fix gcdh · m · (n ∸ m)
  proof₉₋ m n = if-false (fix gcdh · m · (n ∸ m))

------------------------------------------------------------------------------
-- The five equations for gcd

-- First equation.
gcd-00 : gcd zero zero ≡ zero
gcd-00 =
  gcd zero zero         ≡⟨ proof₀₋₁ zero zero ⟩
  gcd-s₁ zero zero      ≡⟨ proof₁₋₂ zero zero ⟩
  gcd-s₂ zero · zero    ≡⟨ proof₂₋₃ zero zero ⟩
  gcd-s₃ zero zero      ≡⟨ proof₃₋₄ zero zero true iszero-0 ⟩
  gcd-s₄ zero zero true ≡⟨ proof₄₊ zero zero ⟩
  zero                  ∎

-- Second equation.
gcd-S0 : ∀ n → gcd (succ₁ n) zero ≡ succ₁ n
gcd-S0 n =
  gcd (succ₁ n) zero         ≡⟨ proof₀₋₁ (succ₁ n) zero ⟩
  gcd-s₁ (succ₁ n) zero      ≡⟨ proof₁₋₂ (succ₁ n) zero ⟩
  gcd-s₂ (succ₁ n) · zero    ≡⟨ proof₂₋₃ (succ₁ n) zero ⟩
  gcd-s₃ (succ₁ n) zero      ≡⟨ proof₃₋₄ (succ₁ n) zero true iszero-0 ⟩
  gcd-s₄ (succ₁ n) zero true ≡⟨ proof₄₊ (succ₁ n) zero ⟩
  succ₁ n                    ∎

-- Third equation.
gcd-0S : ∀ n → gcd zero (succ₁ n) ≡ succ₁ n
gcd-0S n =
  gcd zero (succ₁ n)          ≡⟨ proof₀₋₁ zero (succ₁ n) ⟩
  gcd-s₁ zero (succ₁ n)       ≡⟨ proof₁₋₂ zero (succ₁ n) ⟩
  gcd-s₂ zero · (succ₁ n)     ≡⟨ proof₂₋₃ zero (succ₁ n) ⟩
  gcd-s₃ zero (succ₁ n)       ≡⟨ proof₃₋₄ zero (succ₁ n) false (iszero-S n) ⟩
  gcd-s₄ zero (succ₁ n) false ≡⟨ proof₄₋₆ zero (succ₁ n) ⟩
  gcd-s₆ zero (succ₁ n)       ≡⟨ proof₆₋₇ zero (succ₁ n) true iszero-0 ⟩
  gcd-s₇ zero (succ₁ n) true  ≡⟨ proof₇₊  zero (succ₁ n) ⟩
  succ₁ n                     ∎

-- Fourth equation.
gcd-S>S : ∀ m n → succ₁ m > succ₁ n →
          gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m ∸ succ₁ n) (succ₁ n)

gcd-S>S m n Sm>Sn =
  gcd (succ₁ m) (succ₁ n)
    ≡⟨ proof₀₋₁ (succ₁ m) (succ₁ n) ⟩
  gcd-s₁ (succ₁ m) (succ₁ n)
    ≡⟨ proof₁₋₂ (succ₁ m) (succ₁ n) ⟩
  gcd-s₂ (succ₁ m) · (succ₁ n)
    ≡⟨ proof₂₋₃ (succ₁ m) (succ₁ n) ⟩
  gcd-s₃ (succ₁ m) (succ₁ n)
    ≡⟨ proof₃₋₄ (succ₁ m) (succ₁ n) false (iszero-S n) ⟩
  gcd-s₄ (succ₁ m) (succ₁ n) false
    ≡⟨ proof₄₋₆ (succ₁ m) (succ₁ n) ⟩
  gcd-s₆ (succ₁ m) (succ₁ n)
    ≡⟨ proof₆₋₇ (succ₁ m) (succ₁ n) false (iszero-S m) ⟩
  gcd-s₇ (succ₁ m) (succ₁ n) false
    ≡⟨ proof₇₋₈ (succ₁ m) (succ₁ n) ⟩
  gcd-s₈ (succ₁ m) (succ₁ n)
    ≡⟨ proof₈₋₉ (succ₁ m) (succ₁ n) true Sm>Sn ⟩
  gcd-s₉ (succ₁ m) (succ₁ n) true
    ≡⟨ proof₉₊  (succ₁ m) (succ₁ n) ⟩
  fix gcdh · (succ₁ m ∸ succ₁ n) · succ₁ n ∎

-- Fifth equation.
gcd-S≯S : ∀ m n → succ₁ m ≯ succ₁ n →
          gcd (succ₁ m) (succ₁ n) ≡ gcd (succ₁ m) (succ₁ n ∸ succ₁ m)
gcd-S≯S m n Sm≯Sn =
  gcd (succ₁ m) (succ₁ n)
    ≡⟨ proof₀₋₁ (succ₁ m) (succ₁ n) ⟩
  gcd-s₁ (succ₁ m) (succ₁ n)
    ≡⟨ proof₁₋₂ (succ₁ m) (succ₁ n) ⟩
  gcd-s₂ (succ₁ m) · (succ₁ n)
    ≡⟨ proof₂₋₃ (succ₁ m) (succ₁ n) ⟩
  gcd-s₃ (succ₁ m) (succ₁ n)
    ≡⟨ proof₃₋₄ (succ₁ m) (succ₁ n) false (iszero-S n) ⟩
  gcd-s₄ (succ₁ m) (succ₁ n) false
    ≡⟨ proof₄₋₆ (succ₁ m) (succ₁ n) ⟩
  gcd-s₆ (succ₁ m) (succ₁ n)
    ≡⟨ proof₆₋₇ (succ₁ m) (succ₁ n) false (iszero-S m) ⟩
  gcd-s₇ (succ₁ m) (succ₁ n) false
    ≡⟨ proof₇₋₈ (succ₁ m) (succ₁ n) ⟩
  gcd-s₈ (succ₁ m) (succ₁ n)
    ≡⟨ proof₈₋₉ (succ₁ m) (succ₁ n) false Sm≯Sn ⟩
  gcd-s₉ (succ₁ m) (succ₁ n) false
    ≡⟨ proof₉₋ (succ₁ m) (succ₁ n) ⟩
  fix gcdh · succ₁ m · (succ₁ n ∸ succ₁ m) ∎
