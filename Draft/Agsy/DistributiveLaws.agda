------------------------------------------------------------------------------
-- Asgy test on distributive laws on a binary operation
------------------------------------------------------------------------------

module DistributiveLaws where

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

-- Properties

Stanovsky1 : ∀ u x y z → (x · y · (z · u)) ·
                        (( x · y · ( z · u)) · (x · z · (y · u))) ≡
                        x · z · (y · u)
Stanovsky1 u x y z = {!-t 20 -m!}  -- Agsy fails

Stanovsky : ∀ u x y z → (x · y · (z · u)) ·
                        (( x · y · ( z · u)) · (x · z · (y · u))) ≡
                        x · z · (y · u)
Stanovsky u x y z =
-- The numbering of the justifications correspond to the numbers of
-- the proof using only equational reasoning (see
-- DistributiveLaws.Interactive.Properties).
  begin
    xy·zu · (xy·zu · xz·yu)                                         ≡⟨ j₁ ⟩

    xy·zu · (xz · xu·yu · (y·zu · xz·yu))                           ≡⟨ j₅ ⟩

    xy·zu · (xz · xyu · (yxz · yu))                                 ≡⟨ j₉ ⟩

    xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu))              ≡⟨ j₁₄ ⟩

    xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡⟨ j₂₀ ⟩

    xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))            ≡⟨ j₂₃ ⟩

    (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))                 ≡⟨ j₂₅ ⟩

    xz · xyu · (y·zy · xzu)                                         ≡⟨ j₃₀ ⟩

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

    j₁ : xy·zu · (xy·zu · xz·yu) ≡
         xy·zu · (xz · xu·yu · (y·zu · xz·yu))
    j₁ = {!-t 20 -m !}  -- Agsy fails

    j₅ : xy·zu · (xz · xu·yu · (y·zu · xz·yu)) ≡
         xy·zu · (xz · xyu · (yxz · yu))
    j₅ = {!-t 20 -m !}  -- Agsy fails

    j₉ : xy·zu · (xz · xyu · (yxz · yu)) ≡
         xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu))
    j₉ = {!-t 20 -m!}  -- Agsy fails

    j₁₄ : xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu)) ≡
          xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
    j₁₄ = {!-t 20 -m!}  -- Agsy fails

    j₂₀ : xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡
          xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))
    j₂₀ = {!-t 20 -m!}  -- Agsy fails

    j₂₃ : xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu))) ≡
          (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))
    j₂₃ = {!-t 20 -m!}  -- Agsy fails

    j₂₅ : (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu)) ≡
          xz · xyu · (y·zy · xzu)

    j₂₅ = {!-t 20 -m!}  -- Agsy fails

    j₃₀ : xz · xyu · (y·zy · xzu) ≡
          xz·yu
    j₃₀ = {!-t 20 -m!}  -- Agsy fails
