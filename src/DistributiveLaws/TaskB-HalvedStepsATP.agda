------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DistributiveLaws.TaskB-HalvedStepsATP where

open import DistributiveLaws.Base

open import Common.FOL.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

-- We prove the half of the proof steps (skipping the even ones) of
-- DistributiveLaws.TaskB-I using the ATPs.

prop₂ : ∀ u x y z → (x · y · (z · u)) ·
                    (( x · y · ( z · u)) · (x · z · (y · u))) ≡
                    x · z · (y · u)
prop₂ u x y z =

-- The numbering of the proof step justifications are associated with
-- the numbers used in DistributiveLaws.TaskB-I.

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

  xz·yu ∎
  where
  -- Two variables abbreviations

  xz = x · z
  yu = y · u
  yz = y · z
  zy = z · y
  {-# ATP definition xz #-}
  {-# ATP definition yu #-}
  {-# ATP definition yz #-}
  {-# ATP definition zy #-}

  -- Three variables abbreviations

  xyu = x · y · u
  xzu = x · z · u
  xzy = x · z · y
  yxz = y · x · z
  {-# ATP definition xyu #-}
  {-# ATP definition xzu #-}
  {-# ATP definition xzy #-}
  {-# ATP definition yxz #-}

  x·zu = x · (z · u)
  x·zy = x · (z · y)
  {-# ATP definition x·zu #-}
  {-# ATP definition x·zy #-}

  y·xu = y · (x · u)
  y·yu = y · (y · u)
  y·zu = y · (z · u)
  y·zy = y · (z · y)
  {-# ATP definition y·xu  #-}
  {-# ATP definition y·yu  #-}
  {-# ATP definition y·zu  #-}
  {-# ATP definition y·zy  #-}

  z·xu = z · (x · u)
  z·yu = z · (y · u)
  {-# ATP definition z·xu  #-}
  {-# ATP definition z·yu  #-}

  -- Four variables abbreviations

  xu·yu = x · u · (y · u)
  xu·zu = x · u · (z · u)
  {-# ATP definition xu·yu  #-}
  {-# ATP definition xu·zu  #-}

  xy·zu = x · y · (z · u)
  {-# ATP definition xy·zu  #-}

  xz·xy = x · z · (x · y)
  xz·yu = x · z · (y · u)
  xz·yz = x · z · (y · z)
  {-# ATP definition xz·xy  #-}
  {-# ATP definition xz·yu  #-}
  {-# ATP definition xz·yz  #-}

  yz·yu = y · z · (y · u)
  {-# ATP definition yz·yu  #-}

  zy·xu = z · y · (x · u)
  zy·zu = z · y · (z · u)
  {-# ATP definition zy·xu  #-}
  {-# ATP definition zy·zu  #-}

  -- Steps justifications

  postulate
    j₁₋₃   : xy·zu · (xy·zu · xz·yu) ≡
             xy·zu · (x·zu · xz·yu · (y·zu · xz·yu))
  {-# ATP prove j₁₋₃ #-}

  -- 2012-02-23: Only Equinox 5.0alpha (2010-06-29) proved the theorem (180 sec).
  postulate
    j₃₋₅   : xy·zu · (x·zu · xz·yu · (y·zu · xz·yu)) ≡
             xy·zu · (xz · xu·yu · (y·zu · xz·yu))
  {-# ATP prove j₃₋₅ #-}

  postulate
    j₅₋₇   : xy·zu · (xz · xu·yu · (y·zu · xz·yu)) ≡
             xy·zu · (xz · xyu · (yz·yu · xz·yu))
  {-# ATP prove j₅₋₇ #-}

  postulate
    j₇₋₉   : xy·zu · (xz · xyu · (yz·yu · xz·yu)) ≡
             xy·zu · (xz · xyu · (yxz · yu))
  {-# ATP prove j₇₋₉ #-}

  postulate
    j₉₋₁₁  : xy·zu · (xz · xyu · (yxz · yu)) ≡
             xy·zu · (xz · xyu · (y·xu · z·yu))
  {-# ATP prove j₉₋₁₁ #-}

  postulate
    j₁₁₋₁₃ : xy·zu · (xz · xyu · (y·xu · z·yu)) ≡
             xz·yz · xyu · (xz · xyu · (y·xu · z·yu))
  {-# ATP prove j₁₁₋₁₃ #-}

  -- 2012-02-23: Only Equinox 5.0alpha (2010-06-29) proved the theorem (180 sec).
  postulate
    j₁₃₋₁₅ : xz·yz · xyu · (xz · xyu · (y·xu · z·yu)) ≡
             xz · xyu · (yz · xyu · (y·xu · z·yu))
  {-# ATP prove j₁₃₋₁₅ #-}

  postulate
    j₁₅₋₁₇ : xz · xyu · (yz · xyu · (y·xu · z·yu)) ≡
             xz · xyu · (y · xu·yu · (z · xu·yu) · (y·xu · z·yu))
  {-# ATP prove j₁₅₋₁₇ #-}

  postulate
    j₁₇₋₁₉ : xz · xyu · (y · xu·yu · (z · xu·yu) · (y·xu · z·yu)) ≡
             xz · xyu ·
             (y·xu · y·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₁₇₋₁₉ #-}

  -- 2012-02-23: Only Equinox 5.0alpha (2010-06-29) proved the theorem (180 sec).
  postulate
    j₁₉₋₂₁ : xz · xyu ·
             (y·xu · y·yu · (y·xu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡
             xz · xyu · (y·xu · yz·yu · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₁₉₋₂₁ #-}

  postulate
    j₂₁₋₂₃ : xz · xyu · (y·xu · yz·yu · (z · xu·yu · (y·xu · z·yu))) ≡
             xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₂₁₋₂₃ #-}

  -- 2012-02-23: Only Equinox 5.0alpha (2010-06-29) proved the theorem (180 sec).
  postulate
    j₂₃₋₂₅ : xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu))) ≡
             (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))
  {-# ATP prove j₂₃₋₂₅ #-}

  postulate
    j₂₅₋₂₇ : (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu)) ≡
             xz · xyu · (y · xu·zu · (zy·xu · zy·zu))
  {-# ATP prove j₂₅₋₂₇ #-}

  -- 2012-02-23: Only Equinox 5.0alpha (2010-06-29) proved the theorem (180 sec).
  postulate
    j₂₇₋₂₉ : xz · xyu · (y · xu·zu · (zy·xu · zy·zu)) ≡
             xz · xyu · (y·zy · xu·zu)
  {-# ATP prove j₂₇₋₂₉ #-}

  postulate
    j₂₉₋₃₁ : xz · xyu · (y·zy · xu·zu) ≡
             xz·xy · xzu · (y·zy · xzu)
  {-# ATP prove j₂₉₋₃₁ #-}

  postulate
    j₃₁₋₃₃ : xz·xy · xzu · (y·zy · xzu) ≡
             x·zy · y·zy · xzu
  {-# ATP prove j₃₁₋₃₃ #-}

  postulate
    j₃₃₋₃₅ : x·zy · y·zy · xzu ≡
             xzy · xzu
  {-# ATP prove j₃₃₋₃₅ #-}

  postulate
    j₃₅    : xzy · xzu ≡
             xz·yu
  {-# ATP prove j₃₅ #-}
