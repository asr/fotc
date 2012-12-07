{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}
{-# OPTIONS --universal-quantified-formulae #-}

module CombiningProofs.CommDisjunctionSchema where

open import Common.FOL.FOL

postulate ∨-comm : {A B : Set} → A ∨ B → B ∨ A
{-# ATP prove ∨-comm #-}
