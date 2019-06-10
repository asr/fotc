------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Lemma 4
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.DistributiveLaws.Lemma4 where

open import Combined.DistributiveLaws.Base

------------------------------------------------------------------------------

postulate lemma-4a : ∀ x y z → ((x · x ) · y) · z ≡ (x · y) · z
{-# ATP prove lemma-4a #-}

postulate lemma-4b : ∀ x y z → (x · (y · (z · z))) ≡ x · (y · z)
{-# ATP prove lemma-4b #-}
