------------------------------------------------------------------------------
-- Distributive groupoids properties (using the ATPs and equational reasoning)
------------------------------------------------------------------------------

module GroupTheory.Groupoids.PropertiesATP-ER3 where

open import GroupTheory.Groupoids.Base

open import Common.Relation.Binary.EqReasoning using ( _≡⟨_⟩_ ; _∎ ; begin_ )
open import Common.Relation.Binary.PropositionalEquality.PropertiesER
  using ( subst )

------------------------------------------------------------------------------

-- In this module we prove the proposition 2 of [1] (see the reference
-- for the paper proof) using a combination of interactive and
-- automatic methodologies.

-- 1. ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ (x ∙ z)
-- 2. ∀ x y z → (x ∙ y) ∙ z ≡ (x ∙ z) ∙ (y ∙ z)
-- ----------------------------------------------
-- ∀ u x y z → (x ∙ y ∙ (z ∙ u)) ∙
--             (( x ∙ y ∙ ( z ∙ u)) ∙ (x ∙ z ∙ (y ∙ u))) ≡
--             x ∙ z ∙ (y ∙ u)

-- [1] David Stanovský. Distributive groupoids are
-- symmetrical-by-medial: An elementary proof. Commentations
-- Mathematicae Universitatis Carolinae, 49(4):541–546, 2008.

Stanovsky : ∀ u x y z → (x ∙ y ∙ (z ∙ u)) ∙
                        (( x ∙ y ∙ ( z ∙ u)) ∙ (x ∙ z ∙ (y ∙ u))) ≡
                        x ∙ z ∙ (y ∙ u)
Stanovsky u x y z =
-- The numbering of the justifications correspond to the numbers of
-- the proof using only equational reasoning (see
-- GroupTheory.Groupoids.PropertiesER).
  begin
    xy∙zu ∙ (xy∙zu ∙ xz∙yu)                                         ≡⟨ j₁ ⟩

    xy∙zu ∙ (xz ∙ xu∙yu ∙ (y∙zu ∙ xz∙yu))                           ≡⟨ j₅ ⟩

    xy∙zu ∙ (xz ∙ xyu ∙ (yxz ∙ yu))                                 ≡⟨ j₉ ⟩

    xz ∙ xyu ∙ (yz ∙ xyu) ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu))              ≡⟨ j₁₄ ⟩

    xz ∙ xyu ∙ (y∙xu ∙ (y∙yu ∙ z∙yu) ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu))) ≡⟨ j₂₀ ⟩

    xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))            ≡⟨ j₂₃ ⟩

    (xz ∙ xyu) ∙ (y ∙ xu∙zu ∙ (z∙xu ∙ y∙xu ∙ z∙yu))                 ≡⟨ j₂₅ ⟩

    xz ∙ xyu ∙ (y∙zy ∙ xzu)                                         ≡⟨ j₃₀ ⟩

    xz∙yu
  ∎
  where
    -- Two variables abbreviations

    xz = x ∙ z
    yu = y ∙ u
    yz = y ∙ z
    {-# ATP definition xz #-}
    {-# ATP definition yu #-}
    {-# ATP definition yz #-}

    -- Three variables abbreviations

    xyu = x ∙ y ∙ u
    xyz = x ∙ y ∙ z
    xzu = x ∙ z ∙ u
    yxz = y ∙ x ∙ z
    {-# ATP definition xyu #-}
    {-# ATP definition xyz #-}
    {-# ATP definition xzu #-}
    {-# ATP definition yxz #-}

    y∙xu = y ∙ (x ∙ u)
    y∙yu = y ∙ (y ∙ u)
    y∙zu = y ∙ (z ∙ u)
    y∙zy = y ∙ (z ∙ y)
    {-# ATP definition y∙xu  #-}
    {-# ATP definition y∙yu  #-}
    {-# ATP definition y∙zu  #-}
    {-# ATP definition y∙zy  #-}

    z∙xu = z ∙ (x ∙ u)
    z∙yu = z ∙ (y ∙ u)
    {-# ATP definition z∙xu  #-}
    {-# ATP definition z∙yu  #-}

    -- Four variables abbreviations

    xu∙yu = x ∙ u ∙ (y ∙ u)
    xu∙zu = x ∙ u ∙ (z ∙ u)
    {-# ATP definition xu∙yu  #-}
    {-# ATP definition xu∙zu  #-}

    xy∙zu = x ∙ y ∙ (z ∙ u)
    {-# ATP definition xy∙zu  #-}

    xz∙yu = x ∙ z ∙ (y ∙ u)
    {-# ATP definition xz∙yu  #-}

    -- Steps justifications

    postulate
      j₁ : xy∙zu ∙ (xy∙zu ∙ xz∙yu) ≡
           xy∙zu ∙ (xz ∙ xu∙yu ∙ (y∙zu ∙ xz∙yu))

      j₅ : xy∙zu ∙ (xz ∙ xu∙yu ∙ (y∙zu ∙ xz∙yu)) ≡
           xy∙zu ∙ (xz ∙ xyu ∙ (yxz ∙ yu))

      j₉ : xy∙zu ∙ (xz ∙ xyu ∙ (yxz ∙ yu)) ≡
           xz ∙ xyu ∙ (yz ∙ xyu) ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu))

      j₁₄ : xz ∙ xyu ∙ (yz ∙ xyu) ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu)) ≡
            xz ∙ xyu ∙ (y∙xu ∙ (y∙yu ∙ z∙yu) ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))

      j₂₀ : xz ∙ xyu ∙ (y∙xu ∙ (y∙yu ∙ z∙yu) ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu))) ≡
            xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))

      j₂₃ : xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu))) ≡
            (xz ∙ xyu) ∙ (y ∙ xu∙zu ∙ (z∙xu ∙ y∙xu ∙ z∙yu))

      j₂₅ : (xz ∙ xyu) ∙ (y ∙ xu∙zu ∙ (z∙xu ∙ y∙xu ∙ z∙yu)) ≡
            xz ∙ xyu ∙ (y∙zy ∙ xzu)

      j₃₀ : xz ∙ xyu ∙ (y∙zy ∙ xzu) ≡
            xz∙yu

    {-# ATP prove j₁ #-}
    {-# ATP prove j₅ #-}
    {-# ATP prove j₉ #-}
    {-# ATP prove j₁₄ #-}
    {-# ATP prove j₂₀ #-}
    {-# ATP prove j₂₃ #-}
    {-# ATP prove j₂₅ #-}
    {-# ATP prove j₃₀ #-}
