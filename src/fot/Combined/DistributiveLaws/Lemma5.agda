------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Lemma 5 (Task A)
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.DistributiveLaws.Lemma5 where

open import Combined.DistributiveLaws.Base

------------------------------------------------------------------------------

postulate lemma₅ : ∀ x y → (x · y) · x ≡ x · (y · x)
{-# ATP prove lemma₅ #-}
