{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LogicalFramework.Disjunction where

module LF where
  postulate
    _∨_  : Set → Set → Set
    inj₁ : {A B : Set} → A → A ∨ B
    inj₂ : {A B : Set} → B → A ∨ B
    case : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C

  ∨-comm : {A B : Set} → A ∨ B → B ∨ A
  ∨-comm = case inj₂ inj₁

module Inductive where

  open import Common.FOL.FOL

  ∨-comm-el : {A B : Set} → A ∨ B → B ∨ A
  ∨-comm-el = case inj₂ inj₁

  ∨-comm : {A B : Set} → A ∨ B → B ∨ A
  ∨-comm (inj₁ a) = inj₂ a
  ∨-comm (inj₂ b) = inj₁ b
