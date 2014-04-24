------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Task A
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DistributiveLaws.TaskA-ATP where

open import DistributiveLaws.Base

------------------------------------------------------------------------------
postulate
  lemma₅ : ∀ x y → (x · y) · x ≡ x · (y · x)
{-# ATP prove lemma₅ #-}
