module GroupTheoryER where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- We add 3 to the fixities of the standard library.
infix  11 _⁻¹
infixl 10 _·_  -- The symbol is '\cdot'.

------------------------------------------------------------------------------
-- Group theory axioms
postulate
  G   : Set        -- The group universe.
  ε   : G          -- The identity element.
  _·_ : G → G → G  -- The group binary operation.
  _⁻¹ : G → G      -- The inverse function.

  associativity : (x y z : G) → x · y · z    ≡ x · (y · z)
  leftIdentity  : (x : G)     →     ε · x    ≡ x
  rightIdentity : (x : G)     →     x · ε    ≡ x
  leftInverse   : (x : G)     →  x ⁻¹ · x    ≡ ε
  rightInverse  : (x : G)     →  x    · x ⁻¹ ≡ ε

-- Properties

leftCancellation : (x y z : G) → x · y ≡ x · z → y ≡ z
leftCancellation x y z x·y≡x·z =
  begin
    y              ≡⟨ sym (leftIdentity y) ⟩
    ε · y          ≡⟨ subst (λ t → ε · y ≡ t · y) (sym (leftInverse x)) refl ⟩
    x ⁻¹ · x · y   ≡⟨ associativity (x ⁻¹) x y ⟩
    x ⁻¹ · (x · y) ≡⟨ subst (λ t → x ⁻¹ · (x · y) ≡ x ⁻¹ · t) x·y≡x·z refl ⟩
    x ⁻¹ · (x · z) ≡⟨ sym (associativity (x ⁻¹) x z) ⟩
    x ⁻¹ · x · z   ≡⟨ subst (λ t → x ⁻¹ · x · z ≡ t · z) (leftInverse x) refl ⟩
    ε · z          ≡⟨ leftIdentity z ⟩
    z
  ∎
