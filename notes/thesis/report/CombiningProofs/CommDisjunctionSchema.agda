{-# OPTIONS --exact-split                     #-}
{-# OPTIONS --no-sized-types                  #-}
{-# OPTIONS --no-universe-polymorphism        #-}
{-# OPTIONS --schematic-propositional-symbols #-}
{-# OPTIONS --without-K                       #-}

module CombiningProofs.CommDisjunctionSchema where

open import Common.FOL.FOL

postulate ∨-comm : {A B : Set} → A ∨ B → B ∨ A
{-# ATP prove ∨-comm #-}
