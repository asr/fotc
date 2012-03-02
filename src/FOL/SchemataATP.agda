------------------------------------------------------------------------------
-- Examples of translation of logical schemata
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOL.SchemataATP where

open import FOL.Base

------------------------------------------------------------------------------

postulate _≡_ : D → D → Set

module NonSchemas where

  postulate
    A B C    : Set
    A¹       : D → Set
    A² B²    : D → D → Set
    A³ B³ C³ : D → D → D → Set
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

  postulate id¹ : ∀ {x} → A¹ x → A¹ x
  {-# ATP prove id¹ #-}

  postulate id² : ∀ {x y} → A² x y → A² x y
  {-# ATP prove id² #-}

  postulate ∨-comm : A ∨ B → B ∨ A
  {-# ATP prove ∨-comm #-}

  postulate ∨-comm² : ∀ {x y} → A² x y ∨ B² x y → B² x y ∨ A² x y
  {-# ATP prove ∨-comm² #-}

  postulate ∧∨-dist : A ∧ (B ∨ C) ↔ A ∧ B ∨ A ∧ C
  {-# ATP prove ∧∨-dist #-}

  postulate
    ∧∨-dist³ : ∀ {x y z} →
               (A³ x y z ∧ (B³ x y z ∨ C³ x y z )) ↔
               (A³ x y z ∧ B³ x y z ∨ A³ x y z ∧ C³ x y z)
  {-# ATP prove ∧∨-dist³ #-}

module Schemas where

  postulate f¹-refl : (f¹ : D → D) → ∀ x → f¹ x ≡ f¹ x
  {-# ATP prove f¹-refl #-}

  postulate f²-refl : (f² : D → D → D) → ∀ x y → f² x y ≡ f² x y
  {-# ATP prove f²-refl #-}

  postulate f³-refl : (f³ : D → D → D → D) → ∀ x y z → f³ x y z ≡ f³ x y z
  {-# ATP prove f³-refl #-}

  postulate id : {A : Set} → A → A
  {-# ATP prove id #-}

  postulate id¹ : {A¹ : D → Set} → ∀ {x} → A¹ x → A¹ x
  {-# ATP prove id¹ #-}

  postulate id² : {A² : D → D → Set} → ∀ {x y} → A² x y → A² x y
  {-# ATP prove id² #-}

  postulate ∨-comm : {A B : Set} → A ∨ B → A ∨ B
  {-# ATP prove ∨-comm #-}

  postulate
    ∨-comm² : {A² B² : D → D → Set} → ∀ {x y} →
              A² x y ∨ B² x y → B² x y ∨ A² x y
  {-# ATP prove ∨-comm² #-}

  postulate ∧∨-dist : {A B C : Set} → A ∧ (B ∨ C) ↔ A ∧ B ∨ A ∧ C
  {-# ATP prove ∧∨-dist #-}

  postulate
    ∧∨-dist³ : {A³ B³ C³ : D → D → D → Set} → ∀ {x y z} →
               (A³ x y z ∧ (B³ x y z ∨ C³ x y z)) ↔
               (A³ x y z ∧ B³ x y z ∨ A³ x y z ∧ C³ x y z)
  {-# ATP prove ∧∨-dist³ #-}

module SchemaInstances where

  -- A schema
  -- Current translation: ∀ p q x. app(p,x) → app(q,x).
  postulate schema : (A B : D → Set) → ∀ {x} → A x → B x

  -- Using the current translation, the ATPs can prove an instance of
  -- the schema.
  postulate
    d         : D
    A B       : D → Set
    instanceC : A d → B d
  {-# ATP prove instanceC schema #-}
