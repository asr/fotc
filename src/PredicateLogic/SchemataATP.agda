------------------------------------------------------------------------------
-- Examples of translation of logical schemata
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PredicateLogic.SchemataATP where

open import PredicateLogic.Constants

------------------------------------------------------------------------------

postulate _≡_ : D → D → Set

module NonSchemas where

  postulate
    P Q R    : Set
    P₁       : D → Set
    P₂ Q₂    : D → D → Set
    P₃ Q₃ R₃ : D → D → D → Set
    f₁       : D → D
    f₂       : D → D → D
    f₃       : D → D → D → D

  postulate f₁-refl : ∀ x → f₁ x ≡ f₁ x
  {-# ATP prove f₁-refl #-}

  postulate f₂-refl : ∀ x y → f₂ x y ≡ f₂ x y
  {-# ATP prove f₂-refl #-}

  postulate f₃-refl : ∀ x y z  → f₃ x y z ≡ f₃ x y z
  {-# ATP prove f₃-refl #-}

  postulate id : P → P
  {-# ATP prove id #-}

  postulate id₁ : ∀ {x} → P₁ x → P₁ x
  {-# ATP prove id₁ #-}

  postulate id₂ : ∀ {x y} → P₂ x y → P₂ x y
  {-# ATP prove id₂ #-}

  postulate ∨-comm : P ∨ Q → Q ∨ P
  {-# ATP prove ∨-comm #-}

  postulate ∨-comm₂ : ∀ {x y} → P₂ x y ∨ Q₂ x y → Q₂ x y ∨ P₂ x y
  {-# ATP prove ∨-comm₂ #-}

  postulate ∧∨-dist : P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R
  {-# ATP prove ∧∨-dist #-}

  postulate
    ∧∨-dist₃ : ∀ {x y z} →
               (P₃ x y z ∧ (Q₃ x y z ∨ R₃ x y z )) ↔
               (P₃ x y z ∧ Q₃ x y z ∨ P₃ x y z ∧ R₃ x y z)
  {-# ATP prove ∧∨-dist₃ #-}

module Schemas where

  postulate f₁-refl : (f₁ : D → D) → ∀ x → f₁ x ≡ f₁ x
  {-# ATP prove f₁-refl #-}

  postulate f₂-refl : (f₂ : D → D → D) → ∀ x y → f₂ x y ≡ f₂ x y
  {-# ATP prove f₂-refl #-}

  postulate f₃-refl : (f₃ : D → D → D → D) → ∀ x y z → f₃ x y z ≡ f₃ x y z
  {-# ATP prove f₃-refl #-}

  postulate id : {P : Set} → P → P
  {-# ATP prove id #-}

  postulate id₁ : {P₁ : D → Set} → ∀ {x} → P₁ x → P₁ x
  {-# ATP prove id₁ #-}

  postulate id₂ : {P₂ : D → D → Set} → ∀ {x y} → P₂ x y → P₂ x y
  {-# ATP prove id₂ #-}

  postulate ∨-comm : {P Q : Set} → P ∨ Q → Q ∨ P
  {-# ATP prove ∨-comm #-}

  postulate
    ∨-comm₂ : {P₂ Q₂ : D → D → Set} → ∀ {x y} →
              P₂ x y ∨ Q₂ x y → Q₂ x y ∨ P₂ x y
  {-# ATP prove ∨-comm₂ #-}

  postulate ∧∨-dist : {P Q R : Set} → P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R
  {-# ATP prove ∧∨-dist #-}

  postulate
    ∧∨-dist₃ : {P₃ Q₃ R₃ : D → D → D → Set} → ∀ {x y z} →
               (P₃ x y z ∧ (Q₃ x y z ∨ R₃ x y z)) ↔
               (P₃ x y z ∧ Q₃ x y z ∨ P₃ x y z ∧ R₃ x y z)
  {-# ATP prove ∧∨-dist₃ #-}

module SchemaInstances where

  -- A schema
  -- Current translation: ∀ p q x. app(p,x) → app(q,x).
  postulate schema : (P Q : D → Set) → ∀ {x} → P x → Q x

  -- Using the current translation, the ATPs can prove an instance of
  -- the schema.
  postulate
    d         : D
    P Q       : D → Set
    instanceC : P d → Q d
  {-# ATP prove instanceC schema #-}
