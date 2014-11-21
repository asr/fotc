------------------------------------------------------------------------------
-- Conversion rules for the division
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.Division.ConversionRulesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Program.Division.Division

------------------------------------------------------------------------------
-- Division properties

private
    -- Before to prove some properties for div it is convenient
    -- to have a proof for each possible execution step.

    -- Initially, we define the possible states (div-s₁, div-s₂, ...)
    -- and after that, we write down the proof for the execution step
    -- from the state p to the state q, e.g.
    --
    -- proof₂₋₃ : ∀ i j → div-s₂ i j ≡ div-s₃ i j.

    -- Initially, the conversion rule div-eq is applied.
    div-s₁ : D → D → D
    div-s₁ i j = if (lt i j) then zero else succ₁ (div (i ∸ j) j)

    -- lt i j ≡ true.
    div-s₂ : D → D → D
    div-s₂ i j = if true
                   then zero
                   else succ₁ (div (i ∸ j) j)

    -- lt i j ≡ false.
    div-s₃ : D → D → D
    div-s₃ i j = if false
                   then zero
                   else succ₁ (div (i ∸ j) j)

    -- The conditional is true.
    div-s₄ : D
    div-s₄ = zero

    -- The conditional is false.
    div-s₅ : D → D → D
    div-s₅ i j = succ₁ (div (i ∸ j) j)

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

    -- From div i j to div-s₁ using the equation div-eq.
    proof₀₋₁ : ∀ i j → div i j ≡ div-s₁ i j
    proof₀₋₁ i j = div-eq i j

    -- From div-s₁ to div-s₂ using the proof i<j.
    proof₁₋₂ : ∀ i j → i < j → div-s₁ i j ≡ div-s₂ i j
    proof₁₋₂ i j i<j =
      subst (λ t → (if t
                      then zero
                      else succ₁ (div (i ∸ j) j))
                   ≡
                   (if true
                      then zero
                      else succ₁ (div (i ∸ j) j))
            )
            (sym i<j)
            refl

    -- From div-s₁ to div-s₃ using the proof i≮j.
    proof₁₋₃ : ∀ i j → i ≮ j → div-s₁ i j ≡ div-s₃ i j
    proof₁₋₃ i j i≮j =
      subst (λ t → (if t
                      then zero
                      else succ₁ (div (i ∸ j) j))
                   ≡
                   (if false
                      then zero
                      else succ₁ (div (i ∸ j) j))
            )
            (sym i≮j)
            refl

    -- From div-s₂ to div-s₄ using the conversion rule if-true.
    proof₂₋₄ : ∀ i j → div-s₂ i j ≡ div-s₄
    proof₂₋₄ i j = if-true zero

    -- From div-s₃ to div-s₅ using the conversion rule if-false.
    proof₃₋₅ : ∀ i j → div-s₃ i j ≡ div-s₅ i j
    proof₃₋₅ i j = if-false (succ₁ (div (i ∸ j) j))

----------------------------------------------------------------------
-- The division result when the dividend is minor than the
-- the divisor.
div-x<y : ∀ {i j} → i < j → div i j ≡ zero
div-x<y {i} {j} i<j =
  div i j    ≡⟨ proof₀₋₁ i j ⟩
  div-s₁ i j ≡⟨ proof₁₋₂ i j i<j ⟩
  div-s₂ i j ≡⟨ proof₂₋₄ i j ⟩
  div-s₄     ∎

----------------------------------------------------------------------
-- The division result when the dividend is greater or equal than the
-- the divisor.
div-x≮y : ∀ {i j} → i ≮ j → div i j ≡ succ₁ (div (i ∸ j) j)
div-x≮y {i} {j} i≮j =
  div i j    ≡⟨ proof₀₋₁ i j ⟩
  div-s₁ i j ≡⟨ proof₁₋₃ i j i≮j ⟩
  div-s₃ i j ≡⟨ proof₃₋₅ i j ⟩
  div-s₅ i j ∎
