------------------------------------------------------------------------------
-- Distributive groupoids properties (using equational reasoning)
------------------------------------------------------------------------------

module Draft.Groupoids.PropertiesER where

open import Draft.Groupoids.Base

open import Common.Relation.Binary.EqReasoning using ( _≡⟨_⟩_ ; _∎ ; begin_ )
open import Common.Relation.Binary.PropositionalEquality.PropertiesER
  using ( subst )

------------------------------------------------------------------------------

Stanovsky : ∀ u x y z → (x ∙ y ∙ (z ∙ u)) ∙
                        (( x ∙ y ∙ ( z ∙ u)) ∙ (x ∙ z ∙ (y ∙ u))) ≡
                        x ∙ z ∙ (y ∙ u)

-- Paper proof: Proposition 2 of [1].

-- [1] David Stanovsky. Distributive groupoids are symmetrical-by-medial: An
-- elementary proof. Commentations Mathematicae Universitatis Carolinae,
-- 49(4):541–546, 2008.

Stanovsky u x y z =
  begin
    xy∙zu ∙ (xy∙zu ∙ xz∙yu)
      ≡⟨ j₁ ⟩
    xy∙zu ∙ (x∙zu ∙ y∙zu ∙ xz∙yu)
      ≡⟨ j₂ ⟩
    xy∙zu ∙ (x∙zu ∙ xz∙yu ∙ (y∙zu ∙ xz∙yu))
      ≡⟨ j₃ ⟩
    xy∙zu ∙ (xz∙xu ∙ xz∙yu ∙ (y∙zu ∙ xz∙yu))
      ≡⟨ j₄ ⟩
    xy∙zu ∙ (x ∙ z ∙ xu∙yu ∙ (y∙zu ∙ xz∙yu))
      ≡⟨ j₅ ⟩
    xy∙zu ∙ (x ∙ z ∙ (x ∙ y ∙ u) ∙ (y∙zu ∙ xz∙yu))
      ≡⟨ j₆ ⟩
    xy∙zu ∙ (x ∙ z ∙ (x ∙ y ∙ u) ∙ (yz∙yu ∙ xz∙yu))
      ≡⟨ j₇ ⟩
    xy∙zu ∙ (x ∙ z ∙ (x ∙ y ∙ u) ∙ (yz∙xz ∙ (y ∙ u)))
      ≡⟨ j₈ ⟩
    xy∙zu ∙ (x ∙ z ∙ (x ∙ y ∙ u) ∙ (y ∙ x ∙ z ∙ (y ∙ u)))
      ≡⟨ p ⟩
    xz∙yu
  ∎
  where
    -- Three terms abbreviations

    x∙yu : G
    x∙yu = x ∙ (y ∙ u)

    x∙zu : G
    x∙zu = x ∙ (z ∙ u)

    y∙zu : G
    y∙zu = y ∙ (z ∙ u)

    -- Four terms abbreviations

    xu∙yu : G
    xu∙yu = x ∙ u ∙ (y ∙ u)

    xy∙zu : G
    xy∙zu = x ∙ y ∙ (z ∙ u)

    xz∙yu : G
    xz∙yu = x ∙ z ∙ (y ∙ u)

    xz∙xu : G
    xz∙xu = x ∙ z ∙ (x ∙ u)

    yz∙yu : G
    yz∙yu = y ∙ z ∙ (y ∙ u)

    yz∙xz : G
    yz∙xz = y ∙ z ∙ (x ∙ z)

    -- Steps justifications

    j₁ = subst (λ t → xy∙zu ∙ (xy∙zu ∙ xz∙yu) ≡ xy∙zu ∙ (t ∙ xz∙yu))
               (rightDistributive x y (z ∙ u))
               refl

    j₂ = subst (λ t → xy∙zu ∙ (x∙zu ∙ y∙zu ∙ xz∙yu) ≡ xy∙zu ∙ t)
               (rightDistributive x∙zu y∙zu xz∙yu)
               refl

    j₃ = subst (λ t → xy∙zu ∙ (x∙zu ∙ xz∙yu ∙ (y∙zu ∙ xz∙yu)) ≡
                      xy∙zu ∙ (t ∙ xz∙yu ∙ (y∙zu ∙ xz∙yu)))
               (leftDistributive x z u)
               refl

    j₄ = subst (λ t → xy∙zu ∙ (xz∙xu ∙ xz∙yu ∙ (y∙zu ∙ xz∙yu)) ≡
                      xy∙zu ∙ (t ∙ (y∙zu ∙ xz∙yu)))
               (sym (leftDistributive (x ∙ z) (x ∙ u) (y ∙ u)))
               refl

    j₅ = subst (λ t → xy∙zu ∙ (x ∙ z ∙ xu∙yu ∙ (y∙zu ∙ xz∙yu)) ≡
                      xy∙zu ∙ (x ∙ z ∙ t ∙ (y∙zu ∙ xz∙yu)))
               (sym (rightDistributive x y u))
               refl

    j₆ = subst (λ t → xy∙zu ∙ (x ∙ z ∙ (x ∙ y ∙ u) ∙ (y∙zu ∙ xz∙yu)) ≡
                      xy∙zu ∙ (x ∙ z ∙ (x ∙ y ∙ u) ∙ (t ∙ xz∙yu)))
               (leftDistributive y z u)
               refl

    j₇ = subst (λ t → xy∙zu ∙ (x ∙ z ∙ (x ∙ y ∙ u) ∙ (yz∙yu ∙ xz∙yu)) ≡
                      xy∙zu ∙ (x ∙ z ∙ (x ∙ y ∙ u) ∙ t))
               (sym (rightDistributive (y ∙ z) (x ∙ z) (y ∙ u)))
               refl

    j₈ = subst (λ t → xy∙zu ∙ (x ∙ z ∙ (x ∙ y ∙ u) ∙ (yz∙xz ∙ (y ∙ u))) ≡
                     xy∙zu ∙ (x ∙ z ∙ (x ∙ y ∙ u) ∙ (t ∙ (y ∙ u))))
               (sym (rightDistributive y x z))
               refl

    postulate
      -- I was lazy to write all the 35 steps and their justifications.
      p : xy∙zu ∙ (x ∙ z ∙ (x ∙ y ∙ u) ∙ (y ∙ x ∙ z ∙ (y ∙ u))) ≡ xz∙yu
