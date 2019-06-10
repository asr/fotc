------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Task B
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.DistributiveLaws.TaskB-HalvedSteps where

open import Combined.DistributiveLaws.Base

open import Common.FOL.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

-- We prove the half of the proof steps (skipping the even ones) of
-- Combined.DistributiveLaws.TaskB-I using the ATPs.

prop₂ : ∀ u x y z →
        (x · y · (z · u)) · ((x · y · (z · u)) · (x · z · (y · u))) ≡
          x · z · (y · u)
prop₂ u x y z =

-- The numbering of the proof step justifications are associated with
-- the numbers used in Combined.DistributiveLaws.TaskB-I.

  xy·zu · (xy·zu · xz·yu)                                       ≡⟨ j₁₋₃ ⟩
  xy·zu · (x·zu · xz·yu · (y·zu · xz·yu))                       ≡⟨ j₃₋₅ ⟩
  xy·zu · (xz · xu·yu · (y·zu · xz·yu))                         ≡⟨ j₅₋₇ ⟩
  xy·zu · (xz · xyu · (yz·yu · xz·yu))                          ≡⟨ j₇₋₉ ⟩
  xy·zu · (xz · xyu · (yxz · yu))                               ≡⟨ j₉₋₁₁ ⟩
  xy·zu · (xz · xyu · (y·xu · z·yu))                            ≡⟨ j₁₁₋₁₃ ⟩
  xz·yz · xyu · (xz · xyu · (y·xu · z·yu))                      ≡⟨ j₁₃₋₁₅ ⟩
  xz · xyu · (yz · xyu · (y·xu · z·yu))                         ≡⟨ j₁₅₋₁₇ ⟩
  xz · xyu · (y · xu·yu · (z · xu·yu) · (y·xu · z·yu))          ≡⟨ j₁₇₋₁₉ ⟩
  xz · xyu ·
  (y·xu · y·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu)))   ≡⟨ j₁₉₋₂₁ ⟩
  xz · xyu · (y·xu · yz·yu · (z · xu·yu · (y·xu · z·yu)))       ≡⟨ j₂₁₋₂₃ ⟩
  xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))          ≡⟨ j₂₃₋₂₅ ⟩
  (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))               ≡⟨ j₂₅₋₂₇ ⟩
  xz · xyu · (y · xu·zu · (zy·xu · zy·zu))                      ≡⟨ j₂₇₋₂₉ ⟩
  xz · xyu · (y·zy · xu·zu)                                     ≡⟨ j₂₉₋₃₁ ⟩
  xz·xy · xzu · (y·zy · xzu)                                    ≡⟨ j₃₁₋₃₃ ⟩
  x·zy · y·zy · xzu                                             ≡⟨ j₃₃₋₃₅ ⟩
  xzy · xzu                                                     ≡⟨ j₃₅ ⟩
  xz·yu                                                         ∎
  where
  -- Two variables abbreviations

  xz = x · z
  yu = y · u
  yz = y · z
  zy = z · y
  {-# ATP definitions xz yu yz zy #-}

  -- Three variables abbreviations

  xyu = x · y · u
  xzu = x · z · u
  xzy = x · z · y
  yxz = y · x · z
  {-# ATP definitions xyu xzu xzy yxz #-}

  x·zu = x · (z · u)
  x·zy = x · (z · y)
  {-# ATP definitions x·zu x·zy #-}

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

  xy·zu = x · y · (z · u)
  {-# ATP definition xy·zu #-}

  xz·xy = x · z · (x · y)
  xz·yu = x · z · (y · u)
  xz·yz = x · z · (y · z)
  {-# ATP definitions xz·xy xz·yu xz·yz #-}

  yz·yu = y · z · (y · u)
  {-# ATP definition yz·yu #-}

  zy·xu = z · y · (x · u)
  zy·zu = z · y · (z · u)
  {-# ATP definitions zy·xu zy·zu #-}

  -- Steps justifications

  postulate j₁₋₃ : xy·zu · (xy·zu · xz·yu) ≡
                   xy·zu · (x·zu · xz·yu · (y·zu · xz·yu))
  {-# ATP prove j₁₋₃ #-}

  postulate j₃₋₅ : xy·zu · (x·zu · xz·yu · (y·zu · xz·yu)) ≡
                   xy·zu · (xz · xu·yu · (y·zu · xz·yu))
  {-# ATP prove j₃₋₅ #-}

  postulate j₅₋₇ : xy·zu · (xz · xu·yu · (y·zu · xz·yu)) ≡
                   xy·zu · (xz · xyu · (yz·yu · xz·yu))
  {-# ATP prove j₅₋₇ #-}

  postulate j₇₋₉ : xy·zu · (xz · xyu · (yz·yu · xz·yu)) ≡
                   xy·zu · (xz · xyu · (yxz · yu))
  {-# ATP prove j₇₋₉ #-}

  postulate j₉₋₁₁ : xy·zu · (xz · xyu · (yxz · yu)) ≡
                    xy·zu · (xz · xyu · (y·xu · z·yu))
  {-# ATP prove j₉₋₁₁ #-}

  postulate j₁₁₋₁₃ : xy·zu · (xz · xyu · (y·xu · z·yu)) ≡
                     xz·yz · xyu · (xz · xyu · (y·xu · z·yu))
  {-# ATP prove j₁₁₋₁₃ #-}

  postulate j₁₃₋₁₅ : xz·yz · xyu · (xz · xyu · (y·xu · z·yu)) ≡
                     xz · xyu · (yz · xyu · (y·xu · z·yu))
  {-# ATP prove j₁₃₋₁₅ #-}

  postulate j₁₅₋₁₇ : xz · xyu · (yz · xyu · (y·xu · z·yu)) ≡
                     xz · xyu · (y · xu·yu · (z · xu·yu) · (y·xu · z·yu))
  {-# ATP prove j₁₅₋₁₇ #-}

  postulate j₁₇₋₁₉ : xz · xyu · (y · xu·yu · (z · xu·yu) · (y·xu · z·yu)) ≡
                     xz · xyu ·
                    (y·xu · y·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₁₇₋₁₉ #-}

  postulate
    j₁₉₋₂₁ : xz · xyu ·
             (y·xu · y·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡
             xz · xyu · (y·xu · yz·yu · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₁₉₋₂₁ #-}

  postulate
    j₂₁₋₂₃ : xz · xyu · (y·xu · yz·yu · (z · xu·yu · (y·xu · z·yu))) ≡
             xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₂₁₋₂₃ #-}

  postulate j₂₃₋₂₅ : xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu))) ≡
                     (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))
  {-# ATP prove j₂₃₋₂₅ #-}

  postulate j₂₅₋₂₇ : (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu)) ≡
                     xz · xyu · (y · xu·zu · (zy·xu · zy·zu))
  {-# ATP prove j₂₅₋₂₇ #-}

  postulate j₂₇₋₂₉ : xz · xyu · (y · xu·zu · (zy·xu · zy·zu)) ≡
                     xz · xyu · (y·zy · xu·zu)
  {-# ATP prove j₂₇₋₂₉ #-}

  postulate j₂₉₋₃₁ : xz · xyu · (y·zy · xu·zu) ≡
                     xz·xy · xzu · (y·zy · xzu)
  {-# ATP prove j₂₉₋₃₁ #-}

  postulate j₃₁₋₃₃ : xz·xy · xzu · (y·zy · xzu) ≡
                     x·zy · y·zy · xzu
  {-# ATP prove j₃₁₋₃₃ #-}

  postulate j₃₃₋₃₅ : x·zy · y·zy · xzu ≡ xzy · xzu
  {-# ATP prove j₃₃₋₃₅ #-}

  postulate j₃₅ : xzy · xzu ≡ xz·yu
  {-# ATP prove j₃₅ #-}
