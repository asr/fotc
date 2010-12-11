------------------------------------------------------------------------------
-- Distributive groupoids properties
------------------------------------------------------------------------------

module Draft.Groupoids.Properties where

open import Draft.Groupoids.Base

------------------------------------------------------------------------------

postulate
-- From: Proposition 2 of David Stanovsky. Distributive groupoids are
-- symmetrical-by-medial: An elementary
-- proof. Comment. Math. Univ. Carolinae 49/4 (2008), 541--546.

  stanovsky : ∀ u x y z → (x ∙ y ∙ (z ∙ u)) ∙
                          (( x ∙ y ∙ ( z ∙ u)) ∙ (x ∙ z ∙ (y ∙ u))) ≡
                          x ∙ z ∙ (y ∙ u)

-- E 1.2 no-success due to timeout (300 sec).
-- Equinox 5.0alpha (2010-06-29) no-success due to timeout (300 sec).
-- Metis 2.3 (release 20101019) no-success due to timeout (300 sec).
-- {-# ATP prove stanovsky #-}
