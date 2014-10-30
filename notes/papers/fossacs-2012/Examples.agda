{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism        #-}
{-# OPTIONS --schematic-propositional-symbols #-}
{-# OPTIONS --without-K                       #-}

module Examples where

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

postulate commOr : {A B : Set} → A ∨ B → B ∨ A
{-# ATP prove commOr #-}
