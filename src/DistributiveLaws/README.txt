------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation
------------------------------------------------------------------------------

In this directory we prove the proposition 2 (task B) of [1] (see the
reference for the paper proof). Let _∙_ be a binary operation, then

1. ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ (x ∙ z)
2. ∀ x y z → (x ∙ y) ∙ z ≡ (x ∙ z) ∙ (y ∙ z)
----------------------------------------------
∀ u x y z → (x ∙ y ∙ (z ∙ u)) ∙
            (( x ∙ y ∙ ( z ∙ u)) ∙ (x ∙ z ∙ (y ∙ u))) ≡
            x ∙ z ∙ (y ∙ u)

[1] David Stanovský. Distributive groupoids are symmetrical-by-medial:
An elementary proof. Commentations Mathematicae Universitatis
Carolinae, 49(4):541–546, 2008.
