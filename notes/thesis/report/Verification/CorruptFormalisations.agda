{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Verification.CorruptFormalisations where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Base.Loop
open import FOTC.Program.ABP.Terms

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
