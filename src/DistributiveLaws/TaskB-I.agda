------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation
------------------------------------------------------------------------------

module DistributiveLaws.TaskB-I where

open import DistributiveLaws.Base

open import Common.Relation.Binary.EqReasoning using ( _≡⟨_⟩_ ; _∎ ; begin_ )

------------------------------------------------------------------------------

taskB : ∀ u x y z → (x ∙ y ∙ (z ∙ u)) ∙
                    (( x ∙ y ∙ ( z ∙ u)) ∙ (x ∙ z ∙ (y ∙ u))) ≡
                    x ∙ z ∙ (y ∙ u)
taskB u x y z =
  begin
    xy∙zu ∙ (xy∙zu ∙ xz∙yu)                                         ≡⟨ j₁ ⟩

    xy∙zu ∙ (x∙zu ∙ y∙zu ∙ xz∙yu)                                   ≡⟨ j₂ ⟩

    xy∙zu ∙ (x∙zu ∙ xz∙yu ∙ (y∙zu ∙ xz∙yu))                         ≡⟨ j₃ ⟩

    xy∙zu ∙ (xz∙xu ∙ xz∙yu ∙ (y∙zu ∙ xz∙yu))                        ≡⟨ j₄ ⟩

    xy∙zu ∙ (xz ∙ xu∙yu ∙ (y∙zu ∙ xz∙yu))                           ≡⟨ j₅ ⟩

    xy∙zu ∙ (xz ∙ xyu ∙ (y∙zu ∙ xz∙yu))                             ≡⟨ j₆ ⟩

    xy∙zu ∙ (xz ∙ xyu ∙ (yz∙yu ∙ xz∙yu))                            ≡⟨ j₇ ⟩

    xy∙zu ∙ (xz ∙ xyu ∙ (yz∙xz ∙ yu))                               ≡⟨ j₈ ⟩

    xy∙zu ∙ (xz ∙ xyu ∙ (yxz ∙ yu))                                 ≡⟨ j₉ ⟩

    xy∙zu ∙ (xz ∙ xyu ∙ (yx∙yu ∙ z∙yu))                             ≡⟨ j₁₀ ⟩

    xy∙zu ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu))                              ≡⟨ j₁₁ ⟩

    xyz ∙ xyu ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu))                          ≡⟨ j₁₂ ⟩

    xz∙yz ∙ xyu ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu))                        ≡⟨ j₁₃ ⟩

    xz ∙ xyu ∙ (yz ∙ xyu) ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu))              ≡⟨ j₁₄ ⟩

    xz ∙ xyu ∙ (yz ∙ xyu ∙ (y∙xu ∙ z∙yu))                           ≡⟨ j₁₅ ⟩

    xz ∙ xyu ∙ (yz ∙ xu∙yu ∙ (y∙xu ∙ z∙yu))                         ≡⟨ j₁₆ ⟩

    xz ∙ xyu ∙ (y ∙ xu∙yu ∙ (z ∙ xu∙yu) ∙ (y∙xu ∙ z∙yu))            ≡⟨ j₁₇ ⟩

    xz ∙ xyu ∙
    (y ∙ xu∙yu ∙ (y∙xu ∙ z∙yu) ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))       ≡⟨ j₁₈ ⟩

    xz ∙ xyu ∙
    (y∙xu ∙ y∙yu ∙ (y∙xu ∙ z∙yu) ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))     ≡⟨ j₁₉ ⟩

    xz ∙ xyu ∙ (y∙xu ∙ (y∙yu ∙ z∙yu) ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu))) ≡⟨ j₂₀ ⟩

    xz ∙ xyu ∙ (y∙xu ∙ yz∙yu ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))         ≡⟨ j₂₁ ⟩

    xz ∙ xyu ∙ (y∙xu ∙ y∙zu ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))          ≡⟨ j₂₂ ⟩

    xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))            ≡⟨ j₂₃ ⟩

    xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (z∙xu ∙ z∙yu ∙ (y∙xu ∙ z∙yu)))          ≡⟨ j₂₄ ⟩

    (xz ∙ xyu) ∙ (y ∙ xu∙zu ∙ (z∙xu ∙ y∙xu ∙ z∙yu))                 ≡⟨ j₂₅ ⟩

    xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (zy∙xu ∙ z∙yu))                         ≡⟨ j₂₆ ⟩

    xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (zy∙xu ∙ zy∙zu))                        ≡⟨ j₂₇ ⟩

    xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (zy ∙ xu∙zu))                           ≡⟨ j₂₈ ⟩

    xz ∙ xyu ∙ (y∙zy ∙ xu∙zu)                                       ≡⟨ j₂₉ ⟩

    xz ∙ xyu ∙ (y∙zy ∙ xzu)                                         ≡⟨ j₃₀ ⟩

    xz∙xy ∙ xzu ∙ (y∙zy ∙ xzu)                                      ≡⟨ j₃₁ ⟩

    x∙zy ∙ xzu ∙ (y∙zy ∙ xzu)                                       ≡⟨ j₃₂ ⟩

    x∙zy ∙ y∙zy ∙ xzu                                               ≡⟨ j₃₃ ⟩

    xy∙zy ∙ xzu                                                     ≡⟨ j₃₄ ⟩

    xzy ∙ xzu                                                       ≡⟨ j₃₅ ⟩

    xz∙yu
  ∎
  where
    -- Two variables abbreviations

    xz = x ∙ z
    yu = y ∙ u
    yz = y ∙ z
    zy = z ∙ y

    -- Three variables abbreviations

    xyu = x ∙ y ∙ u
    xyz = x ∙ y ∙ z
    xzu = x ∙ z ∙ u
    xzy = x ∙ z ∙ y
    yxz = y ∙ x ∙ z

    x∙yu = x ∙ (y ∙ u)
    x∙zu = x ∙ (z ∙ u)
    x∙zy = x ∙ (z ∙ y)

    y∙xu = y ∙ (x ∙ u)
    y∙yu = y ∙ (y ∙ u)
    y∙zu = y ∙ (z ∙ u)
    y∙zy = y ∙ (z ∙ y)

    z∙xu = z ∙ (x ∙ u)
    z∙yu = z ∙ (y ∙ u)

    -- Four variables abbreviations

    xu∙yu = x ∙ u ∙ (y ∙ u)
    xu∙zu = x ∙ u ∙ (z ∙ u)

    xy∙yz = x ∙ y ∙ (y ∙ z)
    xy∙zu = x ∙ y ∙ (z ∙ u)
    xy∙zy = x ∙ y ∙ (z ∙ y)

    xz∙xu = x ∙ z ∙ (x ∙ u)
    xz∙xy = x ∙ z ∙ (x ∙ y)
    xz∙yu = x ∙ z ∙ (y ∙ u)
    xz∙yz = x ∙ z ∙ (y ∙ z)

    yx∙yu = y ∙ x ∙ (y ∙ u)

    yz∙xz = y ∙ z ∙ (x ∙ z)
    yz∙yu = y ∙ z ∙ (y ∙ u)

    zy∙xu = z ∙ y ∙ (x ∙ u)
    zy∙zu = z ∙ y ∙ (z ∙ u)

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

    j₅ = subst (λ t → xy∙zu ∙ (xz ∙ xu∙yu ∙ (y∙zu ∙ xz∙yu)) ≡
                      xy∙zu ∙ (xz ∙ t ∙ (y∙zu ∙ xz∙yu)))
               (sym (rightDistributive x y u))
               refl

    j₆ = subst (λ t → xy∙zu ∙ (xz ∙ xyu ∙ (y∙zu ∙ xz∙yu)) ≡
                      xy∙zu ∙ (xz ∙ xyu ∙ (t ∙ xz∙yu)))
               (leftDistributive y z u)
               refl

    j₇ = subst (λ t → xy∙zu ∙ (xz ∙ xyu ∙ (yz∙yu ∙ xz∙yu)) ≡
                      xy∙zu ∙ (xz ∙ xyu ∙ t))
               (sym (rightDistributive (y ∙ z) (x ∙ z) (y ∙ u)))
               refl

    j₈ = subst (λ t → xy∙zu ∙ (xz ∙ xyu ∙ (yz∙xz ∙ yu)) ≡
                      xy∙zu ∙ (xz ∙ xyu ∙ (t ∙ yu)))
               (sym (rightDistributive y x z))
               refl

    j₉ = subst (λ t → xy∙zu ∙ (xz ∙ xyu ∙ (yxz ∙ yu)) ≡
                      xy∙zu ∙ (xz ∙ xyu ∙ t))
               (rightDistributive (y ∙ x) z yu)
               refl

    j₁₀ = subst (λ t → xy∙zu ∙ (xz ∙ xyu ∙ (yx∙yu ∙ z∙yu)) ≡
                       xy∙zu ∙ (xz ∙ xyu ∙ (t ∙ z∙yu)))
                (sym (leftDistributive y x u))
                refl

    j₁₁ = subst (λ t → xy∙zu ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu)) ≡
                       t ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu)))
                (leftDistributive (x ∙ y) z u)
                refl

    j₁₂ = subst (λ t → xyz ∙ xyu ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu)) ≡
                       t ∙ xyu ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu)))
                (rightDistributive x y z)
                refl

    j₁₃ = subst (λ t → xz∙yz ∙ xyu ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu)) ≡
                       t ∙ (xz ∙ xyu ∙ (y∙xu ∙ z∙yu)))
                (rightDistributive (x ∙ z) (y ∙ z) xyu)
                refl

    j₁₄ = sym (leftDistributive (xz ∙ xyu) (yz ∙ xyu) (y∙xu ∙ z∙yu))

    j₁₅ = subst (λ t → xz ∙ xyu ∙ (yz ∙ xyu ∙ (y∙xu ∙ z∙yu)) ≡
                       xz ∙ xyu ∙ (yz ∙ t ∙ (y∙xu ∙ z∙yu)))
                (rightDistributive x y u)
                refl

    j₁₆ = subst (λ t → xz ∙ xyu ∙ (yz ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)) ≡
                       xz ∙ xyu ∙ (t ∙ (y∙xu ∙ z∙yu)))
                (rightDistributive y z xu∙yu)
                refl

    j₁₇ = subst (λ t → xz ∙ xyu ∙ (y ∙ xu∙yu ∙ (z ∙ xu∙yu) ∙ (y∙xu ∙ z∙yu)) ≡
                       xz ∙ xyu ∙ t)
                (rightDistributive (y ∙ xu∙yu) (z ∙ xu∙yu) (y∙xu ∙ z∙yu))
                refl

    j₁₈ = subst (λ t → xz ∙ xyu ∙
                       (y ∙ xu∙yu ∙ (y∙xu ∙ z∙yu) ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))
                       ≡
                       xz ∙ xyu ∙
                       (t ∙ (y∙xu ∙ z∙yu) ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu))))
                (leftDistributive y (x ∙ u) (y ∙ u))
                refl

    j₁₉ = subst (λ t → xz ∙ xyu ∙
                       (y∙xu ∙ y∙yu ∙ (y∙xu ∙ z∙yu) ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))
                       ≡
                       xz ∙ xyu ∙ (t ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu))))
                (sym (leftDistributive y∙xu y∙yu z∙yu))
                refl

    j₂₀ = subst (λ t → xz ∙ xyu ∙
                       (y∙xu ∙ (y∙yu ∙ z∙yu) ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))
                       ≡
                       xz ∙ xyu ∙
                       (y∙xu ∙ t ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu))))
                (sym (rightDistributive y z (y ∙ u)))
                refl

    j₂₁ = subst (λ t → xz ∙ xyu ∙
                       (y∙xu ∙ yz∙yu ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))
                       ≡
                       xz ∙ xyu ∙
                       (y∙xu ∙ t ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu))))
                (sym (leftDistributive y z u))
                refl

    j₂₂ = subst (λ t → xz ∙ xyu ∙
                       (y∙xu ∙ y∙zu ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu)))
                       ≡
                       xz ∙ xyu ∙
                       (t ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu))))
                (sym (leftDistributive y (x ∙ u) (z ∙ u)))
                refl

    j₂₃ = subst (λ t → xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (z ∙ xu∙yu ∙ (y∙xu ∙ z∙yu))) ≡
                       xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (t ∙ (y∙xu ∙ z∙yu))))
                (leftDistributive z (x ∙ u) (y ∙ u))
                refl

    j₂₄ = subst (λ t → xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (z∙xu ∙ z∙yu ∙ (y∙xu ∙ z∙yu))) ≡
                       xz ∙ xyu ∙ (y ∙ xu∙zu ∙ t))
                (sym (rightDistributive z∙xu y∙xu z∙yu))
                refl

    j₂₅ = subst (λ t → xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (z∙xu ∙ y∙xu ∙ z∙yu)) ≡
                       xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (t ∙ z∙yu)))
                (sym (rightDistributive z y (x ∙ u)))
                refl

    j₂₆ = subst (λ t → xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (zy∙xu ∙ z∙yu)) ≡
                       xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (zy∙xu ∙ t)))
                (leftDistributive z y u)
                refl

    j₂₇ = subst (λ t → xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (zy∙xu ∙ zy∙zu)) ≡
                       xz ∙ xyu ∙ (y ∙ xu∙zu ∙ t))
                (sym (leftDistributive (z ∙ y) (x ∙ u) (z ∙ u)))
                refl

    j₂₈ = subst (λ t → xz ∙ xyu ∙ (y ∙ xu∙zu ∙ (zy ∙ xu∙zu)) ≡ xz ∙ xyu ∙ t)
                (sym (rightDistributive y zy xu∙zu))
                refl

    j₂₉ = subst (λ t → xz ∙ xyu ∙ (y∙zy ∙ xu∙zu) ≡ xz ∙ xyu ∙ (y∙zy ∙ t))
                (sym (rightDistributive x z u))
                refl

    j₃₀ = subst (λ t → xz ∙ xyu ∙ (y∙zy ∙ xzu) ≡ t ∙ (y∙zy ∙ xzu))
                (leftDistributive xz (x ∙ y) u)
                refl

    j₃₁ = subst (λ t → xz∙xy ∙ xzu ∙ (y∙zy ∙ xzu) ≡ (t ∙ xzu ∙ (y∙zy ∙ xzu)))
                (sym (leftDistributive x z y))
                refl

    j₃₂ = sym (rightDistributive x∙zy y∙zy xzu)

    j₃₃ = subst (λ t → x∙zy ∙ y∙zy ∙ xzu ≡ t ∙ xzu)
                (sym (rightDistributive x y zy))
                refl

    j₃₄ = subst (λ t → xy∙zy ∙ xzu ≡ t ∙ xzu)
                (sym (rightDistributive x z y))
                refl

    j₃₅ = sym (leftDistributive xz y u)
