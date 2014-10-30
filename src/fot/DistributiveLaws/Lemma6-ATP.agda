------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Lemma 6
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module DistributiveLaws.Lemma6-ATP where

open import DistributiveLaws.Base

------------------------------------------------------------------------------

postulate
  lemma₆ : ∀ u x y z →
           (((x · y) · (z · u)) · ((x · y) · (z · u))) ≡ (x · y) · (z · u)
{-# ATP prove lemma₆ #-}
