------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation
------------------------------------------------------------------------------

In this directory we prove the proposition 2 (task B) of [1].  Let _·_
be a left-associative binary operation, the task B consist in given
the left and right distributive axioms

∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ (x ∙ z)
∀ x y z → (x ∙ y) ∙ z ≡ (x ∙ z) ∙ (y ∙ z)

to prove the theorem

∀ u x y z → (x ∙ y ∙ (z ∙ u)) ∙
            (( x ∙ y ∙ ( z ∙ u)) ∙ (x ∙ z ∙ (y ∙ u))) ≡
            x ∙ z ∙ (y ∙ u)

[1] David Stanovský. Distributive groupoids are symmetrical-by-medial:
    An elementary proof. Commentations Mathematicae Universitatis
    Carolinae, 49(4):541–546, 2008.
