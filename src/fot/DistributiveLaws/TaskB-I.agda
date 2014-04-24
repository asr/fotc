------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Task B
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DistributiveLaws.TaskB-I where

open import DistributiveLaws.Base
open import DistributiveLaws.PropertiesI

open import Common.FOL.Relation.Binary.EqReasoning

------------------------------------------------------------------------------
prop₂ : ∀ u x y z →
        (x · y · (z · u)) · ((x · y · (z · u)) · (x · z · (y · u))) ≡
          x · z · (y · u)
prop₂ u x y z =
  xy·zu · (xy·zu · xz·yu)                                         ≡⟨ j₁ ⟩
  xy·zu · (x·zu · y·zu · xz·yu)                                   ≡⟨ j₂ ⟩
  xy·zu · (x·zu · xz·yu · (y·zu · xz·yu))                         ≡⟨ j₃ ⟩
-- Note: The paper proof has a typo in the third proof step:
-- xy·zu · (xz·xu · xz·yu · (z·zu · xz·yu))
  xy·zu · (xz·xu · xz·yu · (y·zu · xz·yu))                        ≡⟨ j₄ ⟩
  xy·zu · (xz · xu·yu · (y·zu · xz·yu))                           ≡⟨ j₅ ⟩
  xy·zu · (xz · xyu · (y·zu · xz·yu))                             ≡⟨ j₆ ⟩
  xy·zu · (xz · xyu · (yz·yu · xz·yu))                            ≡⟨ j₇ ⟩
  xy·zu · (xz · xyu · (yz·xz · yu))                               ≡⟨ j₈ ⟩
  xy·zu · (xz · xyu · (yxz · yu))                                 ≡⟨ j₉ ⟩
  xy·zu · (xz · xyu · (yx·yu · z·yu))                             ≡⟨ j₁₀ ⟩
  xy·zu · (xz · xyu · (y·xu · z·yu))                              ≡⟨ j₁₁ ⟩
  xyz · xyu · (xz · xyu · (y·xu · z·yu))                          ≡⟨ j₁₂ ⟩
  xz·yz · xyu · (xz · xyu · (y·xu · z·yu))                        ≡⟨ j₁₃ ⟩
  xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu))              ≡⟨ j₁₄ ⟩
  xz · xyu · (yz · xyu · (y·xu · z·yu))                           ≡⟨ j₁₅ ⟩
  xz · xyu · (yz · xu·yu · (y·xu · z·yu))                         ≡⟨ j₁₆ ⟩
  xz · xyu · (y · xu·yu · (z · xu·yu) · (y·xu · z·yu))            ≡⟨ j₁₇ ⟩
  xz · xyu ·
  (y · xu·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu)))       ≡⟨ j₁₈ ⟩
  xz · xyu ·
  (y·xu · y·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu)))     ≡⟨ j₁₉ ⟩
  xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡⟨ j₂₀ ⟩
  xz · xyu · (y·xu · yz·yu · (z · xu·yu · (y·xu · z·yu)))         ≡⟨ j₂₁ ⟩
  xz · xyu · (y·xu · y·zu · (z · xu·yu · (y·xu · z·yu)))          ≡⟨ j₂₂ ⟩
  xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))            ≡⟨ j₂₃ ⟩
  xz · xyu · (y · xu·zu · (z·xu · z·yu · (y·xu · z·yu)))          ≡⟨ j₂₄ ⟩
  (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))                 ≡⟨ j₂₅ ⟩
  xz · xyu · (y · xu·zu · (zy·xu · z·yu))                         ≡⟨ j₂₆ ⟩
  xz · xyu · (y · xu·zu · (zy·xu · zy·zu))                        ≡⟨ j₂₇ ⟩
  xz · xyu · (y · xu·zu · (zy · xu·zu))                           ≡⟨ j₂₈ ⟩
  xz · xyu · (y·zy · xu·zu)                                       ≡⟨ j₂₉ ⟩
  xz · xyu · (y·zy · xzu)                                         ≡⟨ j₃₀ ⟩
  xz·xy · xzu · (y·zy · xzu)                                      ≡⟨ j₃₁ ⟩
  x·zy · xzu · (y·zy · xzu)                                       ≡⟨ j₃₂ ⟩
  x·zy · y·zy · xzu                                               ≡⟨ j₃₃ ⟩
  xy·zy · xzu                                                     ≡⟨ j₃₄ ⟩
  xzy · xzu                                                       ≡⟨ j₃₅ ⟩
  xz·yu                                                           ∎
  where
  -- Two variables abbreviations

  xz = x · z
  yu = y · u
  yz = y · z
  zy = z · y

  -- Three variables abbreviations

  xyu = x · y · u
  xyz = x · y · z
  xzu = x · z · u
  xzy = x · z · y
  yxz = y · x · z

  x·yu = x · (y · u)
  x·zu = x · (z · u)
  x·zy = x · (z · y)

  y·xu = y · (x · u)
  y·yu = y · (y · u)
  y·zu = y · (z · u)
  y·zy = y · (z · y)

  z·xu = z · (x · u)
  z·yu = z · (y · u)

  -- Four variables abbreviations

  xu·yu = x · u · (y · u)
  xu·zu = x · u · (z · u)

  xy·yz = x · y · (y · z)
  xy·zu = x · y · (z · u)
  xy·zy = x · y · (z · y)

  xz·xu = x · z · (x · u)
  xz·xy = x · z · (x · y)
  xz·yu = x · z · (y · u)
  xz·yz = x · z · (y · z)

  yx·yu = y · x · (y · u)

  yz·xz = y · z · (x · z)
  yz·yu = y · z · (y · u)

  zy·xu = z · y · (x · u)
  zy·zu = z · y · (z · u)

  -- Steps justifications

  j₁ : xy·zu · (xy·zu · xz·yu) ≡
       xy·zu · (x·zu · y·zu · xz·yu)
  j₁ = ·-rightCong (·-leftCong (rightDistributive x y (z · u)))

  j₂ : xy·zu · (x·zu · y·zu · xz·yu) ≡
       xy·zu · (x·zu · xz·yu · (y·zu · xz·yu))
  j₂ = ·-rightCong (rightDistributive x·zu y·zu xz·yu)

  j₃ : xy·zu · (x·zu · xz·yu · (y·zu · xz·yu)) ≡
       xy·zu · (xz·xu · xz·yu · (y·zu · xz·yu))
  j₃ = ·-rightCong (·-leftCong (·-leftCong (leftDistributive x z u)))

  j₄ : xy·zu · (xz·xu · xz·yu · (y·zu · xz·yu)) ≡
       xy·zu · (xz · xu·yu · (y·zu · xz·yu))
  j₄ = ·-rightCong (·-leftCong (sym (leftDistributive (x · z) (x · u) (y · u))))

  j₅ : xy·zu · (xz · xu·yu · (y·zu · xz·yu)) ≡
       xy·zu · (xz · xyu · (y·zu · xz·yu))
  j₅ = ·-rightCong (·-leftCong (·-rightCong (sym (rightDistributive x y u))))

  j₆ : xy·zu · (xz · xyu · (y·zu · xz·yu)) ≡
       xy·zu · (xz · xyu · (yz·yu · xz·yu))
  j₆ = ·-rightCong (·-rightCong (·-leftCong (leftDistributive y z u)))

  j₇ : xy·zu · (xz · xyu · (yz·yu · xz·yu)) ≡
       xy·zu · (xz · xyu · (yz·xz · yu))
  j₇ = ·-rightCong (·-rightCong (sym (rightDistributive (y · z) (x · z) (y · u))))

  j₈ : xy·zu · (xz · xyu · (yz·xz · yu)) ≡
       xy·zu · (xz · xyu · (yxz · yu))
  j₈ = ·-rightCong (·-rightCong (·-leftCong (sym (rightDistributive y x z))))

  j₉ : xy·zu · (xz · xyu · (yxz · yu)) ≡
       xy·zu · (xz · xyu · (yx·yu · z·yu))
  j₉ = ·-rightCong (·-rightCong (rightDistributive (y · x) z yu))

  j₁₀ : xy·zu · (xz · xyu · (yx·yu · z·yu)) ≡
        xy·zu · (xz · xyu · (y·xu · z·yu))
  j₁₀ = ·-rightCong (·-rightCong (·-leftCong (sym (leftDistributive y x u))))

  j₁₁ : xy·zu · (xz · xyu · (y·xu · z·yu)) ≡
        xyz · xyu · (xz · xyu · (y·xu · z·yu))
  j₁₁ = ·-leftCong (leftDistributive (x · y) z u)

  j₁₂ : xyz · xyu · (xz · xyu · (y·xu · z·yu)) ≡
        xz·yz · xyu · (xz · xyu · (y·xu · z·yu))
  j₁₂ = ·-leftCong (·-leftCong (rightDistributive x y z))

  j₁₃ : xz·yz · xyu · (xz · xyu · (y·xu · z·yu)) ≡
        xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu))
  j₁₃ = ·-leftCong (rightDistributive (x · z) (y · z) xyu)

  j₁₄ : xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu)) ≡
        xz · xyu · (yz · xyu · (y·xu · z·yu))
  j₁₄ = sym (leftDistributive (xz · xyu) (yz · xyu) (y·xu · z·yu))

  j₁₅ : xz · xyu · (yz · xyu · (y·xu · z·yu)) ≡
        xz · xyu · (yz · xu·yu · (y·xu · z·yu))
  j₁₅ = ·-rightCong (·-leftCong (·-rightCong (rightDistributive x y u)))

  j₁₆ : xz · xyu · (yz · xu·yu · (y·xu · z·yu)) ≡
        xz · xyu · (y · xu·yu · (z · xu·yu) · (y·xu · z·yu))
  j₁₆ = ·-rightCong (·-leftCong (rightDistributive y z xu·yu))

  j₁₇ : xz · xyu · (y · xu·yu · (z · xu·yu) · (y·xu · z·yu)) ≡
        xz · xyu ·
        (y · xu·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
  j₁₇ = subst (λ t → xz · xyu · (y · xu·yu · (z · xu·yu) · (y·xu · z·yu)) ≡
                     xz · xyu · t)
              (rightDistributive (y · xu·yu) (z · xu·yu) (y·xu · z·yu))
              refl

  j₁₈ : xz · xyu ·
        (y · xu·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡
        xz · xyu ·
        (y·xu · y·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
  j₁₈ = ·-rightCong (·-leftCong (·-leftCong (leftDistributive y (x · u) (y · u))))

  j₁₉ : xz · xyu ·
        (y·xu · y·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡
        xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
  j₁₉ = subst (λ t → xz · xyu ·
                     (y·xu · y·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
                     ≡
                     xz · xyu · (t · (z · xu·yu · (y·xu · z·yu))))
              (sym (leftDistributive y·xu y·yu z·yu))
              refl

  j₂₀ : xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡
        xz · xyu · (y·xu · yz·yu · (z · xu·yu · (y·xu · z·yu)))
  j₂₀ = ·-rightCong (·-leftCong (·-rightCong (sym (rightDistributive y z (y · u)))))

  j₂₁ : xz · xyu · (y·xu · yz·yu · (z · xu·yu · (y·xu · z·yu))) ≡
        xz · xyu · (y·xu · y·zu · (z · xu·yu · (y·xu · z·yu)))
  j₂₁ = ·-rightCong (·-leftCong (·-rightCong (sym (leftDistributive y z u))))

  j₂₂ : xz · xyu · (y·xu · y·zu · (z · xu·yu · (y·xu · z·yu))) ≡
        xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))
  j₂₂ = ·-rightCong (·-leftCong (sym (leftDistributive y (x · u) (z · u))))

  j₂₃ : xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu))) ≡
        xz · xyu · (y · xu·zu · (z·xu · z·yu · (y·xu · z·yu)))
  j₂₃ = ·-rightCong (·-rightCong (·-leftCong (leftDistributive z (x · u) (y · u))))

  j₂₄ : xz · xyu · (y · xu·zu · (z·xu · z·yu · (y·xu · z·yu))) ≡
        (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))
  j₂₄ = ·-rightCong (·-rightCong (sym (rightDistributive z·xu y·xu z·yu)))

  j₂₅ : (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu)) ≡
        xz · xyu · (y · xu·zu · (zy·xu · z·yu))
  j₂₅ = ·-rightCong (·-rightCong (·-leftCong (sym (rightDistributive z y (x · u)))))

  j₂₆ : xz · xyu · (y · xu·zu · (zy·xu · z·yu)) ≡
        xz · xyu · (y · xu·zu · (zy·xu · zy·zu))
  j₂₆ = ·-rightCong (·-rightCong (·-rightCong (leftDistributive z y u)))

  j₂₇ : xz · xyu · (y · xu·zu · (zy·xu · zy·zu)) ≡
        xz · xyu · (y · xu·zu · (zy · xu·zu))
  j₂₇ = ·-rightCong (·-rightCong (sym (leftDistributive (z · y) (x · u) (z · u))))

  j₂₈ : xz · xyu · (y · xu·zu · (zy · xu·zu)) ≡
        xz · xyu · (y·zy · xu·zu)
  j₂₈ = ·-rightCong (sym (rightDistributive y zy xu·zu))

  j₂₉ : xz · xyu · (y·zy · xu·zu) ≡
        xz · xyu · (y·zy · xzu)
  j₂₉ = ·-rightCong (·-rightCong (sym (rightDistributive x z u)))


  j₃₀ : xz · xyu · (y·zy · xzu) ≡
        xz·xy · xzu · (y·zy · xzu)
  j₃₀ = ·-leftCong (leftDistributive xz (x · y) u)

  j₃₁ : xz·xy · xzu · (y·zy · xzu) ≡
        x·zy · xzu · (y·zy · xzu)
  j₃₁ = ·-leftCong (·-leftCong (sym (leftDistributive x z y)))

  j₃₂ : x·zy · xzu · (y·zy · xzu) ≡
        x·zy · y·zy · xzu
  j₃₂ = sym (rightDistributive x·zy y·zy xzu)

  j₃₃ : x·zy · y·zy · xzu ≡
        xy·zy · xzu
  j₃₃ = ·-leftCong (sym (rightDistributive x y zy))

  j₃₄ : xy·zy · xzu ≡
        xzy · xzu
  j₃₄ = ·-leftCong (sym (rightDistributive x z y))

  j₃₅ : xzy · xzu ≡
        xz·yu
  j₃₅ = sym (leftDistributive xz y u)
