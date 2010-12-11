------------------------------------------------------------------------------
-- Distributive groupoids properties
------------------------------------------------------------------------------

module GroupTheory.Groupoids.Properties where

open import GroupTheory.Groupoids.Base

------------------------------------------------------------------------------

postulate
-- From: Proposition 2 of [1].

-- [1] David Stanovsky. Distributive groupoids are symmetrical-by-medial: An
-- elementary proof. Commentations Mathematicae Universitatis Carolinae,
-- 49(4):541–546, 2008.
  Stanovsky : ∀ u x y z → (x ∙ y ∙ (z ∙ u)) ∙
                          (( x ∙ y ∙ ( z ∙ u)) ∙ (x ∙ z ∙ (y ∙ u))) ≡
                          x ∙ z ∙ (y ∙ u)

-- E 1.2 no-success due to timeout (300 sec).
-- Equinox 5.0alpha (2010-06-29) no-success due to timeout (300 sec).
-- Metis 2.3 (release 20101019) no-success due to timeout (300 sec).
-- {-# ATP prove Stanovsky #-}
