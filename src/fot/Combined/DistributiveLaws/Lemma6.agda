------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Lemma 6
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.DistributiveLaws.Lemma6 where

open import Combined.DistributiveLaws.Base

------------------------------------------------------------------------------

postulate
  lemma₆ : ∀ u x y z →
           (((x · y) · (z · u)) · ((x · y) · (z · u))) ≡ (x · y) · (z · u)
{-# ATP prove lemma₆ #-}
