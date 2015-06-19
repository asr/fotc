------------------------------------------------------------------------------
-- Examples of translation of logical schemata
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

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
               (A³ x y z ∧ (B³ x y z ∨ C³ x y z)) ↔
               (A³ x y z ∧ B³ x y z ∨ A³ x y z ∧ C³ x y z)
  {-# ATP prove ∧∨-dist³ #-}

module Schemas where

  postulate id : {A : Set} → A → A
  {-# ATP prove id #-}

  postulate id¹ : {A¹ : D → Set} → ∀ {x} → A¹ x → A¹ x
  {-# ATP prove id¹ #-}

  postulate id² : {A² : D → D → Set} → ∀ {x y} → A² x y → A² x y
  {-# ATP prove id² #-}

  postulate ∨-comm : {A B : Set} → A ∨ B → A ∨ B
  {-# ATP prove ∨-comm #-}

  postulate ∨-comm² : {A² B² : D → D → Set} → ∀ {x y} →
                      A² x y ∨ B² x y → B² x y ∨ A² x y
  {-# ATP prove ∨-comm² #-}

  postulate ∧∨-dist : {A B C : Set} → A ∧ (B ∨ C) ↔ A ∧ B ∨ A ∧ C
  {-# ATP prove ∧∨-dist #-}

  postulate ∧∨-dist³ : {A³ B³ C³ : D → D → D → Set} → ∀ {x y z} →
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
