------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Lemma 3
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DistributiveLaws.Lemma3-ATP where

open import DistributiveLaws.Base

------------------------------------------------------------------------------
postulate lemma₃ : ∀ x y z → (x · y) · (z · z) ≡ (x · y) · z
{-# ATP prove lemma₃ #-}
