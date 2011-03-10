------------------------------------------------------------------------------
-- Examples of translation of logical schemas
------------------------------------------------------------------------------

module Logic.SchemasATP where

open import Logic.Constants

------------------------------------------------------------------------------

postulate
  _≡_ : D → D → Set

module NonSchemas where

  postulate
    P Q R : Set
    f₁    : D → D
    f₂    : D → D → D
    f₃    : D → D → D → D

  postulate
    f₁-refl : (x : D) → f₁ x ≡ f₁ x
  {-# ATP prove f₁-refl #-}

  postulate
    f₂-refl : (x y : D) → f₂ x y ≡ f₂ x y
  {-# ATP prove f₂-refl #-}

  postulate
    f₃-refl : (x y z : D) → f₃ x y z ≡ f₃ x y z
  {-# ATP prove f₃-refl #-}

  postulate
    ∧-ident : P ∧ ⊤ ↔ P
  {-# ATP prove ∧-ident #-}

  postulate
    ∨-comm  : P ∨ Q → Q ∨ P
  {-# ATP prove ∨-comm #-}

  postulate
    ∧∨-dist : P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R
  {-# ATP prove ∧∨-dist #-}

module Schemas where

  postulate
    f₁-refl : (f₁ : D → D)(x : D) → f₁ x ≡ f₁ x
  {-# ATP prove f₁-refl #-}

  postulate
    f₂-refl : (f₂ : D → D → D)(x y : D) → f₂ x y ≡ f₂ x y
  {-# ATP prove f₂-refl #-}

  postulate
    f₃-refl : (f₃ : D → D → D → D)(x y z : D) → f₃ x y z ≡ f₃ x y z
  {-# ATP prove f₃-refl #-}

  postulate
    ∧-ident : {P : Set} → P ∧ ⊤ ↔ P
  {-# ATP prove ∧-ident #-}

  postulate
    ∨-comm  : {P Q : Set} → P ∨ Q → Q ∨ P
  {-# ATP prove ∨-comm #-}

  postulate
    ∧∨-dist : {P Q R : Set} → P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R
  {-# ATP prove ∧∨-dist #-}
