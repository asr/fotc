{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Verification.CorruptFormalisations where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Base.Loop
open import Combined.FOTC.Program.ABP.Terms

------------------------------------------------------------------------------

-- Corrupt as a constant.
module Constant where
  postulate
    corrupt   : D
    corrupt-T : ∀ os x xs →
                corrupt · (T ∷ os) · (x ∷ xs) ≡ ok x ∷ corrupt · os · xs
    corrupt-F : ∀ os x xs →
                corrupt · (F ∷ os) · (x ∷ xs) ≡ error ∷ corrupt · os · xs

-- Corrupt as a binary function.
module BinaryFunction where
  postulate
    corrupt   : D → D → D
    corrupt-T : ∀ os x xs →
                corrupt (T ∷ os) (x ∷ xs) ≡ ok x ∷ corrupt os xs
    corrupt-F : ∀ os x xs →
                corrupt (F ∷ os) (x ∷ xs) ≡ error ∷ corrupt os xs
