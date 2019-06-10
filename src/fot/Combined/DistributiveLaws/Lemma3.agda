------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Lemma 3
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.DistributiveLaws.Lemma3 where

open import Combined.DistributiveLaws.Base

------------------------------------------------------------------------------

postulate lemma₃ : ∀ x y z → (x · y) · (z · z) ≡ (x · y) · z
{-# ATP prove lemma₃ #-}
