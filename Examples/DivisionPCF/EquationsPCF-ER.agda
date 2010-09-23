------------------------------------------------------------------------------
-- Equations for the division
------------------------------------------------------------------------------

module Examples.DivisionPCF.EquationsPCF-ER where

open import LTC.Minimal
open import LTC.MinimalER using ( subst )

open import Examples.DivisionPCF.DivisionPCF using ( div ; divh )

import Lib.Relation.Binary.EqReasoning
open module APER = Lib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

open import LTC-PCF.DataPCF.NatPCF using ( _-_ ; N )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF using ( _<_ ; GE ; LT )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF.PropertiesPCF-ER
  using ( x≥y→x≮y )

------------------------------------------------------------------------------
-- Division properties

-- Note: This module was written for the version of div using the
-- lambda abstractions, but we can use it with the version of div
-- using super-combinators.

private
    -- Before to prove some properties for 'div i j' it is convenient
    -- to have a proof for each possible execution step.

    -- Initially, we define the possible states ('div-s₁',
    -- 'dih-s₂', ...) and after that, we write down the proof for
    -- the execution step from the state 'p' to the state 'q'
    -- (i.e. (i j : D) → div-sp i j → div-sq i j).

    -- Initially, 'cFix' conversion rule is applied
    div-s₁ : D → D → D
    div-s₁ i j = divh (fix divh) ∙ i ∙ j

    -- First argument application
    div-s₂ : D → D → D
    div-s₂ i j = fun ∙ j
      where fun : D
            fun = lam (λ j → if (i < j)
                                then zero
                                else (succ (fix divh ∙ (i - j) ∙ j)))

    -- Second argument application
    div-s₃ : D → D → D
    div-s₃ i j = if (i < j)
                    then zero
                    else (succ (fix divh ∙ (i - j) ∙ j))

    -- 'lt i j ≡ true'
    div-s₄ : D → D → D
    div-s₄ i j = if true
                    then zero
                    else (succ (fix divh ∙ (i - j) ∙ j))

    -- 'lt i j ≡ false'
    div-s₅ : D → D → D
    div-s₅ i j = if false
                    then zero
                    else (succ (fix divh ∙ (i - j) ∙ j))

    -- The conditional is 'true'
    div-s₆ : D
    div-s₆ = zero

    -- The conditional is 'false'
    div-s₇ : D → D → D
    div-s₇ i j = succ (fix divh ∙ (i - j) ∙ j)

    {-
    To prove the execution steps
    (e.g. proof₃₋₄ : (i j : D) → div-s₃ i j → divh_s₄ i j),
    we usually need to prove that

                             '... m ... ≡ ... n ...'    (1)

    given that
                                  'm ≡ n',              (2)

    where (2) is a conversion rule usually.
    We prove (1) using
    '≡-subst : {A : Set}(P : A → Set){x y : A} → x ≡ y → P x → P y'
    where
    'P' is given by '\m → ... m ... ≡ ... n ...',
    'x ≡ y' is given 'n ≡ m' (actually, we use '≡-sym (m ≡ n)'), and
    'P x' is given by '... n ... ≡ ... n ...' (i.e. '≡-refl')

    -}

    -- From 'div ∙ i ∙ j' to 'div-s₁' using the conversion rule 'Cfix'
    proof₀₋₁ : (i j : D) → fix divh ∙ i ∙ j  ≡ div-s₁ i j
    proof₀₋₁ i j = subst (λ t → t ∙ i ∙ j ≡ divh (fix divh) ∙ i ∙ j)
                         (sym (cFix divh))
                         refl

    -- From 'div-s₁' to 'div-s₂' using the conversion rule 'beta'
    proof₁₋₂ : (i j : D) → div-s₁ i j  ≡ div-s₂ i j
    proof₁₋₂ i j =
      subst (λ t → t ∙ j ≡ fun i ∙ j)
               (sym (cBeta fun i))
               refl
         where
          -- The function 'fun' is the same that the 'fun' part
          -- of 'div-s₂', except that we need a fresh
          -- variable 'y' to avoid the clashing of the variable 'i' in
          -- the application of the 'beta' rule.
          fun : D → D
          fun y = lam (λ j → if (y < j)
                                then zero
                                else (succ (fix divh ∙ (y - j) ∙ j)))

    -- From 'div-s₂' to 'div-s₃' using the conversion rule 'beta'
    proof₂₋₃ : (i j : D) → div-s₂ i j  ≡ div-s₃ i j
    proof₂₋₃ i j  = cBeta fun j
      where
        -- The function 'fun' is the same that 'div-s₃', except that we
        -- need a fresh 'y' to avoid the clashing of the variable 'j' in
        -- the application of the 'beta' rule.
        fun : D → D
        fun y = if (i < y)
                   then zero
                   else (succ ((fix divh) ∙ (i - y) ∙ y))

    -- From 'div-s₃' to 'div-s₄' using the proof 'i<j'
    proof₃_₄ : (i j : D) → LT i j → div-s₃ i j ≡ div-s₄ i j
    proof₃_₄ i j i<j =
      subst (λ t → if t
                      then zero
                      else (succ ((fix divh) ∙ (i - j) ∙ j))
                      ≡
                   if true
                      then zero
                      else (succ ((fix divh) ∙ (i - j) ∙ j))
            )
            (sym i<j)
            refl

    -- From 'div-s₃' to 'div-s₅' using the proof  'i≥j'
    proof₃₋₅ : {i j : D} → N i → N j → GE i j → div-s₃ i j  ≡ div-s₅ i j
    proof₃₋₅ {i} {j} Ni Nj i≥j =
      subst (λ t → if t
                      then zero
                      else (succ ((fix divh) ∙ (i - j) ∙ j))
                      ≡
                   if false
                      then zero
                      else (succ ((fix divh) ∙ (i - j) ∙ j))
            )
            (sym (x≥y→x≮y Ni Nj i≥j))
            refl

    -- From 'div-s₄' to 'div-s₆' using the conversion rule 'CB1'
    -- ToDo: Why we need to use 'div-s₄ {i} {j}' instead of 'div-s₄'
    proof₄₋₆ : (i j : D) → div-s₄ i j ≡ div-s₆
    proof₄₋₆ i j = cB₁ zero

    -- From 'div-s₅' to 'div-s₇' using the conversion rule 'CB2'
    proof₅₋₇ : (i j : D) → div-s₅ i j ≡ div-s₇ i j
    proof₅₋₇ i j = cB₂ (succ (fix divh ∙ (i - j) ∙ j))

----------------------------------------------------------------------
-- The division result when the dividend is minor than the
-- the divisor

div-x<y : {i j : D} → LT i j → div i j ≡ zero
div-x<y {i} {j} i<j =
  begin
    div i j    ≡⟨ proof₀₋₁ i j ⟩
    div-s₁ i j ≡⟨ proof₁₋₂ i j ⟩
    div-s₂ i j ≡⟨ proof₂₋₃ i j ⟩
    div-s₃ i j ≡⟨ proof₃_₄ i j i<j ⟩
    div-s₄ i j ≡⟨ proof₄₋₆ i j ⟩
    div-s₆
  ∎

----------------------------------------------------------------------
-- The division result when the dividend is greater or equal than the
-- the divisor

div-x≥y : {i j : D} → N i → N j → GE i j →
          div i j ≡ succ (div (i - j) j)
div-x≥y {i} {j} Ni Nj i≥j =
  begin
    div i j    ≡⟨ proof₀₋₁ i j ⟩
    div-s₁ i j ≡⟨ proof₁₋₂ i j ⟩
    div-s₂ i j ≡⟨ proof₂₋₃ i j ⟩
    div-s₃ i j ≡⟨ proof₃₋₅ Ni Nj i≥j ⟩
    div-s₅ i j ≡⟨ proof₅₋₇ i j ⟩
    div-s₇ i j
  ∎
