------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation
------------------------------------------------------------------------------

module DistributiveLaws.TaskB-TopDownATP where

open import DistributiveLaws.Base

open import DistributiveLaws.Relation.Binary.EqReasoning

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
  {-# ATP definition xz #-}
  {-# ATP definition yu #-}
  {-# ATP definition yz #-}

  -- Three variables abbreviations

  xyu = x · y · u
  xyz = x · y · z
  xzu = x · z · u
  yxz = y · x · z
  {-# ATP definition xyu #-}
  {-# ATP definition xyz #-}
  {-# ATP definition xzu #-}
  {-# ATP definition yxz #-}

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

  xz·yu = x · z · (y · u)
  {-# ATP definition xz·yu  #-}

  -- Steps justifications

  postulate
    j₁₋₅   : xy·zu · (xy·zu · xz·yu) ≡
             xy·zu · (xz · xu·yu · (y·zu · xz·yu))
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove j₁₋₅ #-}

  postulate
    j₅₋₉   : xy·zu · (xz · xu·yu · (y·zu · xz·yu)) ≡
             xy·zu · (xz · xyu · (yxz · yu))
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove j₅₋₉ #-}

  postulate
    j₉₋₁₄  : xy·zu · (xz · xyu · (yxz · yu)) ≡
             xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu))
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove j₉₋₁₄ #-}

  postulate
    j₁₄₋₂₀ : xz · xyu · (yz · xyu) · (xz · xyu · (y·xu · z·yu)) ≡
             xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu)))
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove j₁₄₋₂₀ #-}

  postulate
    j₂₀₋₂₃ : xz · xyu · (y·xu · (y·yu · z·yu) · (z · xu·yu · (y·xu · z·yu))) ≡
             xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu)))
  {-# ATP prove j₂₀₋₂₃ #-}

  postulate
    j₂₃₋₂₅ : xz · xyu · (y · xu·zu · (z · xu·yu · (y·xu · z·yu))) ≡
             (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu))
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove j₂₃₋₂₅ #-}

  postulate
    j₂₅₋₃₀ : (xz · xyu) · (y · xu·zu · (z·xu · y·xu · z·yu)) ≡
             xz · xyu · (y·zy · xzu)
  {-# ATP prove j₂₅₋₃₀ #-}

  postulate
    j₃₀₋₃₅ : xz · xyu · (y·zy · xzu) ≡
             xz·yu
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove j₃₀₋₃₅ #-}
