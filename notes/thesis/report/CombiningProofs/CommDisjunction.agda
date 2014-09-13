{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module CombiningProofs.CommDisjunction where

open import Common.FOL.FOL

postulate
  A B : Set
  ∨-comm : A ∨ B → B ∨ A
{-# ATP prove ∨-comm #-}
