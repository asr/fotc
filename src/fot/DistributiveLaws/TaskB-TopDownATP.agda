------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DistributiveLaws.TaskB-TopDownATP where

open import DistributiveLaws.Base

open import Common.FOL.Relation.Binary.EqReasoning

------------------------------------------------------------------------------
-- We found the longest chains of equalities from
-- DistributiveLaws.TaskB-I which are prove by the ATPs, following a
-- top-down approach.

prop₂ : ∀ u x y z → (x · y · (z · u)) ·
                    (( x · y · ( z · u)) · (x · z · (y · u))) ≡
                    x · z · (y · u)
prop₂ u x y z =

-- The numbering of the proof step justifications are associated with
-- the numbers used in DistributiveLaws.TaskB-I.

   xy·zu · (xy·zu · xz·yu)                                         ≡⟨ j₁₋₅ ⟩
   xy·zu · (xz · xu·yu · (y·zu · xz·yu))                           ≡⟨ j₅₋₉ ⟩
   xy·zu · (xz · xyu · (yxz · yu))                                 ≡⟨ j₉₋₁₄ ⟩
   xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu))              ≡⟨ j₁₄₋₂₀ ⟩
   xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡⟨ j₂₀₋₂₃ ⟩
   xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))            ≡⟨ j₂₃₋₂₅ ⟩
   (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))                 ≡⟨ j₂₅₋₃₀ ⟩
   xz · xyu · (y·zy · xzu)                                         ≡⟨ j₃₀₋₃₅ ⟩
   xz·yu                                                           ∎
  where
  -- Two variables abbreviations

  xz = x · z
  yu = y · u
  yz = y · z
  {-# ATP definition xz yu yz #-}

  -- Three variables abbreviations

  xyu = x · y · u
  xyz = x · y · z
  xzu = x · z · u
  yxz = y · x · z
  {-# ATP definition xyu xyz xzu yxz #-}

  y·xu = y · (x · u)
  y·yu = y · (y · u)
  y·zu = y · (z · u)
  y·zy = y · (z · y)
  {-# ATP definition y·xu y·yu y·zu y·zy #-}

  z·xu = z · (x · u)
  z·yu = z · (y · u)
  {-# ATP definition z·xu z·yu #-}

  -- Four variables abbreviations

  xu·yu = x · u · (y · u)
  xu·zu = x · u · (z · u)
  {-# ATP definition xu·yu xu·zu #-}

  xy·zu = x · y · (z · u)
  {-# ATP definition xy·zu #-}

  xz·yu = x · z · (y · u)
  {-# ATP definition xz·yu #-}

  -- Steps justifications

  -- 25 July 2012: Only Equinox 5.0alpha (2010-06-29) proved the theorem (240 sec).
  postulate
    j₁₋₅   : xy·zu · (xy·zu · xz·yu) ≡
             xy·zu · (xz · xu·yu · (y·zu · xz·yu))
  {-# ATP prove j₁₋₅ #-}

  postulate
    j₅₋₉   : xy·zu · (xz · xu·yu · (y·zu · xz·yu)) ≡
             xy·zu · (xz · xyu · (yxz · yu))
  {-# ATP prove j₅₋₉ #-}

  postulate
    j₉₋₁₄  : xy·zu · (xz · xyu · (yxz · yu)) ≡
             xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu))
  {-# ATP prove j₉₋₁₄ #-}

  postulate
    j₁₄₋₂₀ : xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu)) ≡
             xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₁₄₋₂₀ #-}

  postulate
    j₂₀₋₂₃ : xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡
             xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₂₀₋₂₃ #-}

  -- 25 July 2012: Only Equinox 5.0alpha (2010-06-29) proved the theorem (240 sec).
  postulate
    j₂₃₋₂₅ : xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu))) ≡
             (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))
  {-# ATP prove j₂₃₋₂₅ #-}

  postulate
    j₂₅₋₃₀ : (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu)) ≡
             xz · xyu · (y·zy · xzu)
  {-# ATP prove j₂₅₋₃₀ #-}

  postulate
    j₃₀₋₃₅ : xz · xyu · (y·zy · xzu) ≡
             xz·yu
  {-# ATP prove j₃₀₋₃₅ #-}
