------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation via Agsy
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of the standard library on
-- 17 May 2012.

module Agsy.DistributiveLaws.TaskB-TopDown where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- We add 3 to the fixities of the standard library.
infixl 10 _·_  -- The symbol is '\cdot'.

------------------------------------------------------------------------------
-- Distributive laws axioms

postulate
  D   : Set        -- The universe
  _·_ : D → D → D  -- The binary operation.

  leftDistributive  : ∀ x y z → x · (y · z) ≡ (x · y) · (x · z)
  rightDistributive : ∀ x y z → (x · y) · z ≡ (x · z) · (y · z)

-- We test Agsy with the longest chains of equalities from
-- DistributiveLaws.TaskB-TopDownATP.
taskB : ∀ u x y z →
        (x · y · (z · u)) · ((x · y · ( z · u)) · (x · z · (y · u))) ≡
          x · z · (y · u)
taskB u x y z =
-- The numbering of the proof step justifications are associated with
-- the numbers used in DistributiveLaws.TaskB-I.
  begin
    xy·zu · (xy·zu · xz·yu)                                         ≡⟨ j₁₋₅ ⟩
    xy·zu · (xz · xu·yu · (y·zu · xz·yu))                           ≡⟨ j₅₋₉ ⟩
    xy·zu · (xz · xyu · (yxz · yu))                                 ≡⟨ j₉₋₁₄ ⟩
    xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu))              ≡⟨ j₁₄₋₂₀ ⟩
    xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡⟨ j₂₀₋₂₃ ⟩
    xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))            ≡⟨ j₂₃₋₂₅ ⟩
    (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))                 ≡⟨ j₂₅₋₃₀ ⟩
    xz · xyu · (y·zy · xzu)                                         ≡⟨ j₃₀₋₃₅ ⟩
    xz·yu
  ∎
  where
  -- Two variables abbreviations

  xz = x · z
  yu = y · u
  yz = y · z

  -- Three variables abbreviations

  xyu = x · y · u
  xyz = x · y · z
  xzu = x · z · u
  yxz = y · x · z

  y·xu = y · (x · u)
  y·yu = y · (y · u)
  y·zu = y · (z · u)
  y·zy = y · (z · y)

  z·xu = z · (x · u)
  z·yu = z · (y · u)

  -- Four variables abbreviations

  xu·yu = x · u · (y · u)
  xu·zu = x · u · (z · u)

  xy·zu = x · y · (z · u)

  xz·yu = x · z · (y · u)

  -- Steps justifications

  j₁₋₅ : xy·zu · (xy·zu · xz·yu) ≡
         xy·zu · (xz · xu·yu · (y·zu · xz·yu))
  j₁₋₅ = {!-t 20 -m !}  -- Agsy fails

  j₅₋₉ : xy·zu · (xz · xu·yu · (y·zu · xz·yu)) ≡
         xy·zu · (xz · xyu · (yxz · yu))
  j₅₋₉ = {!-t 20 -m !}  -- Agsy fails

  j₉₋₁₄ : xy·zu · (xz · xyu · (yxz · yu)) ≡
          xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu))
  j₉₋₁₄ = {!-t 20 -m!}  -- Agsy fails

  j₁₄₋₂₀ : xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu)) ≡
           xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
  j₁₄₋₂₀ = {!-t 20 -m!}  -- Agsy fails

  j₂₀₋₂₃ : xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡
           xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))
  j₂₀₋₂₃ = {!-t 20 -m!}  -- Agsy fails

  j₂₃₋₂₅ : xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu))) ≡
           (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))
  j₂₃₋₂₅ = {!-t 20 -m!}  -- Agsy fails

  j₂₅₋₃₀ : (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu)) ≡
           xz · xyu · (y·zy · xzu)
  j₂₅₋₃₀ = {!-t 20 -m!}  -- Agsy fails

  j₃₀₋₃₅ : xz · xyu · (y·zy · xzu) ≡
           xz·yu
  j₃₀₋₃₅ = {!-t 20 -m!}  -- Agsy fails
