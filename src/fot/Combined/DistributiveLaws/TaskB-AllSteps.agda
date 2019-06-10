------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Task B
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.DistributiveLaws.TaskB-AllSteps where

open import Combined.DistributiveLaws.Base

open import Common.FOL.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

-- We prove all the proof steps of Combined.DistributiveLaws.TaskB-I using
-- the ATPs.

prop₂ : ∀ u x y z →
        (x · y · (z · u)) · ((x · y · (z · u)) · (x · z · (y · u))) ≡
          x · z · (y · u)
prop₂ u x y z =
  xy·zu · (xy·zu · xz·yu)                                         ≡⟨ j₁ ⟩
  xy·zu · (x·zu · y·zu · xz·yu)                                   ≡⟨ j₂ ⟩
  xy·zu · (x·zu · xz·yu · (y·zu · xz·yu))                         ≡⟨ j₃ ⟩
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
  {-# ATP definitions xz yu yz zy #-}

  -- Three variables abbreviations

  xyu = x · y · u
  xyz = x · y · z
  xzu = x · z · u
  xzy = x · z · y
  yxz = y · x · z
  {-# ATP definitions xyu xyz xzu xzy yxz #-}

  x·yu = x · (y · u)
  x·zu = x · (z · u)
  x·zy = x · (z · y)
  {-# ATP definitions x·yu x·zu x·zy #-}

  y·xu = y · (x · u)
  y·yu = y · (y · u)
  y·zu = y · (z · u)
  y·zy = y · (z · y)
  {-# ATP definitions y·xu y·yu y·zu y·zy #-}

  z·xu = z · (x · u)
  z·yu = z · (y · u)
  {-# ATP definitions z·xu z·yu #-}

  -- Four variables abbreviations

  xu·yu = x · u · (y · u)
  xu·zu = x · u · (z · u)
  {-# ATP definitions xu·yu xu·zu #-}

  xy·yz = x · y · (y · z)
  xy·zu = x · y · (z · u)
  xy·zy = x · y · (z · y)
  {-# ATP definitions xy·yz xy·zu xy·zy #-}

  xz·xu = x · z · (x · u)
  xz·xy = x · z · (x · y)
  xz·yu = x · z · (y · u)
  xz·yz = x · z · (y · z)
  {-# ATP definitions xz·xu xz·xy xz·yu xz·yz #-}

  yx·yu = y · x · (y · u)
  {-# ATP definition yx·yu #-}

  yz·xz = y · z · (x · z)
  yz·yu = y · z · (y · u)
  {-# ATP definitions yz·xz yz·yu #-}

  zy·xu = z · y · (x · u)
  zy·zu = z · y · (z · u)
  {-# ATP definitions zy·xu zy·zu #-}

  -- Steps justifications

  postulate j₁ : xy·zu · (xy·zu · xz·yu) ≡
                 xy·zu · (x·zu · y·zu · xz·yu)
  {-# ATP prove j₁ #-}

  postulate j₂ : xy·zu · (x·zu · y·zu · xz·yu) ≡
                 xy·zu · (x·zu · xz·yu · (y·zu · xz·yu))
  {-# ATP prove j₂ #-}

  postulate j₃ : xy·zu · (x·zu · xz·yu · (y·zu · xz·yu)) ≡
                 xy·zu · (xz·xu · xz·yu · (y·zu · xz·yu))
  {-# ATP prove j₃ #-}

  postulate j₄ : xy·zu · (xz·xu · xz·yu · (y·zu · xz·yu)) ≡
                 xy·zu · (xz · xu·yu · (y·zu · xz·yu))
  {-# ATP prove j₄ #-}

  postulate j₅ : xy·zu · (xz · xu·yu · (y·zu · xz·yu)) ≡
                 xy·zu · (xz · xyu · (y·zu · xz·yu))
  {-# ATP prove j₅ #-}

  postulate j₆ : xy·zu · (xz · xyu · (y·zu · xz·yu)) ≡
                 xy·zu · (xz · xyu · (yz·yu · xz·yu))
  {-# ATP prove j₆ #-}

  postulate j₇ : xy·zu · (xz · xyu · (yz·yu · xz·yu)) ≡
                 xy·zu · (xz · xyu · (yz·xz · yu))
  {-# ATP prove j₇ #-}

  postulate j₈ : xy·zu · (xz · xyu · (yz·xz · yu)) ≡
                 xy·zu · (xz · xyu · (yxz · yu))
  {-# ATP prove j₈ #-}

  postulate j₉ : xy·zu · (xz · xyu · (yxz · yu)) ≡
                 xy·zu · (xz · xyu · (yx·yu · z·yu))
  {-# ATP prove j₉ #-}

  postulate j₁₀ : xy·zu · (xz · xyu · (yx·yu · z·yu)) ≡
                  xy·zu · (xz · xyu · (y·xu · z·yu))
  {-# ATP prove j₁₀ #-}

  postulate j₁₁ : xy·zu · (xz · xyu · (y·xu · z·yu)) ≡
                  xyz · xyu · (xz · xyu · (y·xu · z·yu))
  {-# ATP prove j₁₁ #-}

  postulate j₁₂ : xyz · xyu · (xz · xyu · (y·xu · z·yu)) ≡
                  xz·yz · xyu · (xz · xyu · (y·xu · z·yu))
  {-# ATP prove j₁₂ #-}

  postulate j₁₃ : xz·yz · xyu · (xz · xyu · (y·xu · z·yu)) ≡
                  xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu))
  {-# ATP prove j₁₃ #-}

  postulate j₁₄ : xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu)) ≡
                  xz · xyu · (yz · xyu · (y·xu · z·yu))
  {-# ATP prove j₁₄ #-}

  postulate j₁₅ : xz · xyu · (yz · xyu · (y·xu · z·yu)) ≡
                  xz · xyu · (yz · xu·yu · (y·xu · z·yu))
  {-# ATP prove j₁₅ #-}

  postulate j₁₆ : xz · xyu · (yz · xu·yu · (y·xu · z·yu)) ≡
                  xz · xyu · (y · xu·yu · (z · xu·yu) · (y·xu · z·yu))
  {-# ATP prove j₁₆ #-}

  postulate
    j₁₇ : xz · xyu · (y · xu·yu · (z · xu·yu) · (y·xu · z·yu)) ≡
          xz · xyu ·
          (y · xu·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₁₇ #-}

  postulate
    j₁₈ : xz · xyu ·
          (y · xu·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡
          xz · xyu ·
          (y·xu · y·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₁₈ #-}

  postulate
    j₁₉ : xz · xyu ·
          (y·xu · y·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡
          xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₁₉ #-}

  postulate
    j₂₀ : xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡
          xz · xyu · (y·xu · yz·yu · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₂₀ #-}

  postulate j₂₁ : xz · xyu · (y·xu · yz·yu · (z · xu·yu · (y·xu · z·yu))) ≡
                  xz · xyu · (y·xu · y·zu · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₂₁ #-}

  postulate j₂₂ : xz · xyu · (y·xu · y·zu · (z · xu·yu · (y·xu · z·yu))) ≡
                  xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₂₂ #-}

  postulate j₂₃ : xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu))) ≡
                  xz · xyu · (y · xu·zu · (z·xu · z·yu · (y·xu · z·yu)))
  {-# ATP prove j₂₃ #-}

  postulate j₂₄ : xz · xyu · (y · xu·zu · (z·xu · z·yu · (y·xu · z·yu))) ≡
                  (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))
  {-# ATP prove j₂₄ #-}

  postulate j₂₅ : (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu)) ≡
                  xz · xyu · (y · xu·zu · (zy·xu · z·yu))
  {-# ATP prove j₂₅ #-}

  postulate j₂₆ : xz · xyu · (y · xu·zu · (zy·xu · z·yu)) ≡
                  xz · xyu · (y · xu·zu · (zy·xu · zy·zu))
  {-# ATP prove j₂₆ #-}

  postulate j₂₇ : xz · xyu · (y · xu·zu · (zy·xu · zy·zu)) ≡
                  xz · xyu · (y · xu·zu · (zy · xu·zu))
  {-# ATP prove j₂₇ #-}

  postulate j₂₈ : xz · xyu · (y · xu·zu · (zy · xu·zu)) ≡
                  xz · xyu · (y·zy · xu·zu)
  {-# ATP prove j₂₈ #-}

  postulate j₂₉ : xz · xyu · (y·zy · xu·zu) ≡ xz · xyu · (y·zy · xzu)
  {-# ATP prove j₂₉ #-}

  postulate j₃₀ : xz · xyu · (y·zy · xzu) ≡ xz·xy · xzu · (y·zy · xzu)
  {-# ATP prove j₃₀ #-}

  postulate j₃₁ : xz·xy · xzu · (y·zy · xzu) ≡ x·zy · xzu · (y·zy · xzu)
  {-# ATP prove j₃₁ #-}

  postulate j₃₂ : x·zy · xzu · (y·zy · xzu) ≡ x·zy · y·zy · xzu
  {-# ATP prove j₃₂ #-}

  postulate j₃₃ : x·zy · y·zy · xzu ≡ xy·zy · xzu
  {-# ATP prove j₃₃ #-}

  postulate j₃₄ : xy·zy · xzu ≡ xzy · xzu
  {-# ATP prove j₃₄ #-}

  postulate j₃₅ : xzy · xzu ≡ xz·yu
  {-# ATP prove j₃₅ #-}
