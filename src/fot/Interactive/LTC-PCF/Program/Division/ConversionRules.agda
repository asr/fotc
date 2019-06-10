------------------------------------------------------------------------------
-- Conversion rules for the division
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.LTC-PCF.Program.Division.ConversionRules where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.LTC-PCF.Base
open import Interactive.LTC-PCF.Data.Nat
open import Interactive.LTC-PCF.Data.Nat.Inequalities
open import Interactive.LTC-PCF.Program.Division.Division

------------------------------------------------------------------------------
-- Division properties

private
    -- Before to prove some properties for div it is convenient
    -- to have a proof for each possible execution step.

    -- Initially, we define the possible states (div-s₁, div-s₂,
    -- ...) and after that, we write down the proof for the execution
    -- step from the state p to the state q, e.g.
    --
    -- proof₂₋₃ : ∀ i j → div-s₂ i j ≡ div-s₃ i j.

    -- Initially, the conversion rule fix-eq is applied.
    div-s₁ : D → D → D
    div-s₁ i j = divh (fix divh) · i · j

    -- First argument application.
    div-s₂ : D → D → D
    div-s₂ i j = fun · j
      where
      fun : D
      fun = lam (λ j → if (lt i j)
                         then zero
                         else succ₁ (fix divh · (i ∸ j) · j))

    -- Second argument application.
    div-s₃ : D → D → D
    div-s₃ i j = if (lt i j) then zero else succ₁ (fix divh · (i ∸ j) · j)

    -- lt i j ≡ true.
    div-s₄ : D → D → D
    div-s₄ i j = if true then zero else succ₁ (fix divh · (i ∸ j) · j)

    -- lt i j ≡ false.
    div-s₅ : D → D → D
    div-s₅ i j = if false then zero else succ₁ (fix divh · (i ∸ j) · j)

    -- The conditional is true.
    div-s₆ : D
    div-s₆ = zero

    -- The conditional is false.
    div-s₇ : D → D → D
    div-s₇ i j = succ₁ (fix divh · (i ∸ j) · j)

    {-

    To prove the execution steps, e.g.

    proof₃₋₄ : ∀ i j → div-s₃ i j → divh_s₄ i j,

    we usually need to prove that

                             ... m ... ≡ ... n ...    (1)

    given that
                                  m ≡ n,              (2)

    where (2) is a conversion rule usually.

    We prove (1) using

    subst : ∀ {x y} (A : D → Set) → x ≡ y → A x → A y

    where
      • P is given by \m → ... m ... ≡ ... n ...,
      • x ≡ y is given n ≡ m (actually, we use ≡-sym (m ≡ n)) and
      • P x is given by ... n ... ≡ ... n ... (i.e. ≡-refl)
    -}

    -- From div · i · j to div-s₁ using the conversion rule fix-eq.
    proof₀₋₁ : ∀ i j → fix divh · i · j ≡ div-s₁ i j
    proof₀₋₁ i j = subst (λ t → t · i · j ≡ divh (fix divh) · i · j)
                         (sym (fix-eq divh))
                         refl

    -- From div-s₁ to div-s₂ using the conversion rule beta.
    proof₁₋₂ : ∀ i j → div-s₁ i j ≡ div-s₂ i j
    proof₁₋₂ i j =
      subst (λ t → t · j ≡ fun i · j)
            (sym (beta fun i))
            refl
         where
         -- The function fun is the same that the fun part of div-s₂,
         -- except that we need a fresh variable y to avoid the
         -- clashing of the variable i in the application of the beta
         -- rule.
         fun : D → D
         fun y = lam (λ j → if (lt y j)
                              then zero
                              else succ₁ (fix divh · (y ∸ j) · j))

    -- From div-s₂ to div-s₃ using the conversion rule beta.
    proof₂₋₃ : ∀ i j → div-s₂ i j ≡ div-s₃ i j
    proof₂₋₃ i j  = beta fun j
      where
      -- The function fun is the same that div-s₃, except that we
      -- need a fresh variable y to avoid the clashing of the
      -- variable j in the application of the beta rule.
      fun : D → D
      fun y = if (lt i y) then zero else succ₁ ((fix divh) · (i ∸ y) · y)

    -- From div-s₃ to div-s₄ using the proof i<j.
    proof₃_₄ : ∀ i j → i < j → div-s₃ i j ≡ div-s₄ i j
    proof₃_₄ i j i<j =
      subst (λ t → (if t then zero else succ₁ ((fix divh) · (i ∸ j) · j)) ≡
                   (if true then zero else succ₁ ((fix divh) · (i ∸ j) · j)))
            (sym i<j)
            refl

    -- From div-s₃ to div-s₅ using the proof i≮j.
    proof₃₋₅ : ∀ i j → i ≮ j → div-s₃ i j ≡ div-s₅ i j
    proof₃₋₅ i j i≮j =
      subst (λ t → (if t then zero else succ₁ ((fix divh) · (i ∸ j) · j)) ≡
                   (if false then zero else succ₁ ((fix divh) · (i ∸ j) · j)))
            (sym i≮j)
            refl

    -- From div-s₄ to div-s₆ using the conversion rule if-true.
    proof₄₋₆ : ∀ i j → div-s₄ i j ≡ div-s₆
    proof₄₋₆ i j = if-true zero

    -- From div-s₅ to div-s₇ using the conversion rule if-false.
    proof₅₋₇ : ∀ i j → div-s₅ i j ≡ div-s₇ i j
    proof₅₋₇ i j = if-false (succ₁ (fix divh · (i ∸ j) · j))

----------------------------------------------------------------------
-- The division result when the dividend is minor than the
-- the divisor.
div-x<y : ∀ {i j} → i < j → div i j ≡ zero
div-x<y {i} {j} i<j =
  div i j    ≡⟨ proof₀₋₁ i j ⟩
  div-s₁ i j ≡⟨ proof₁₋₂ i j ⟩
  div-s₂ i j ≡⟨ proof₂₋₃ i j ⟩
  div-s₃ i j ≡⟨ proof₃_₄ i j i<j ⟩
  div-s₄ i j ≡⟨ proof₄₋₆ i j ⟩
  div-s₆     ∎

----------------------------------------------------------------------
-- The division result when the dividend is greater or equal than the
-- the divisor.
div-x≮y : ∀ {i j} → i ≮ j → div i j ≡ succ₁ (div (i ∸ j) j)
div-x≮y {i} {j} i≮j =
  div i j    ≡⟨ proof₀₋₁ i j ⟩
  div-s₁ i j ≡⟨ proof₁₋₂ i j ⟩
  div-s₂ i j ≡⟨ proof₂₋₃ i j ⟩
  div-s₃ i j ≡⟨ proof₃₋₅ i j i≮j ⟩
  div-s₅ i j ≡⟨ proof₅₋₇ i j ⟩
  div-s₇ i j ∎
