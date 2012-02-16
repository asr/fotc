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
    A B C    : Set
    P¹       : D → Set
    P² Q²    : D → D → Set
    P³ Q³ R³ : D → D → D → Set
    f¹       : D → D
    f²       : D → D → D
    f³       : D → D → D → D

  postulate f¹-refl : ∀ x → f¹ x ≡ f¹ x
  {-# ATP prove f¹-refl #-}

  postulate f²-refl : ∀ x y → f² x y ≡ f² x y
  {-# ATP prove f²-refl #-}

  postulate f³-refl : ∀ x y z  → f³ x y z ≡ f³ x y z
  {-# ATP prove f³-refl #-}

  postulate id : A → A
  {-# ATP prove id #-}

  postulate id¹ : ∀ {x} → P¹ x → P¹ x
  {-# ATP prove id¹ #-}

  postulate id² : ∀ {x y} → P² x y → P² x y
  {-# ATP prove id² #-}

  postulate ∨-comm : A ∨ B → B ∨ A
  {-# ATP prove ∨-comm #-}

  postulate ∨-comm² : ∀ {x y} → P² x y ∨ Q² x y → Q² x y ∨ P² x y
  {-# ATP prove ∨-comm² #-}

  postulate ∧∨-dist : A ∧ (B ∨ C) ↔ A ∧ B ∨ A ∧ C
  {-# ATP prove ∧∨-dist #-}

  postulate
    ∧∨-dist³ : ∀ {x y z} →
               (P³ x y z ∧ (Q³ x y z ∨ R³ x y z )) ↔
               (P³ x y z ∧ Q³ x y z ∨ P³ x y z ∧ R³ x y z)
  {-# ATP prove ∧∨-dist³ #-}

module Schemas where

  postulate f¹-refl : (f¹ : D → D) → ∀ x → f¹ x ≡ f¹ x
  {-# ATP prove f¹-refl #-}

  postulate f²-refl : (f² : D → D → D) → ∀ x y → f² x y ≡ f² x y
  {-# ATP prove f²-refl #-}

  postulate f³-refl : (f³ : D → D → D → D) → ∀ x y z → f³ x y z ≡ f³ x y z
  {-# ATP prove f³-refl #-}

  postulate id : {P : Set} → P → P
  {-# ATP prove id #-}

  postulate id¹ : {P¹ : D → Set} → ∀ {x} → P¹ x → P¹ x
  {-# ATP prove id¹ #-}

  postulate id² : {P² : D → D → Set} → ∀ {x y} → P² x y → P² x y
  {-# ATP prove id² #-}

  postulate ∨-comm : {P Q : Set} → P ∨ Q → Q ∨ P
  {-# ATP prove ∨-comm #-}

  postulate
    ∨-comm² : {P² Q² : D → D → Set} → ∀ {x y} →
              P² x y ∨ Q² x y → Q² x y ∨ P² x y
  {-# ATP prove ∨-comm² #-}

  postulate ∧∨-dist : {P Q R : Set} → P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R
  {-# ATP prove ∧∨-dist #-}

  postulate
    ∧∨-dist³ : {P³ Q³ R³ : D → D → D → Set} → ∀ {x y z} →
               (P³ x y z ∧ (Q³ x y z ∨ R³ x y z)) ↔
               (P³ x y z ∧ Q³ x y z ∨ P³ x y z ∧ R³ x y z)
  {-# ATP prove ∧∨-dist³ #-}

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
