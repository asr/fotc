------------------------------------------------------------------------------
-- Distributive laws on a binary operation: Lemma 4
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module DistributiveLaws.Lemma4-ATP where

open import DistributiveLaws.Base

------------------------------------------------------------------------------

postulate lemma-4a : ∀ x y z → ((x · x ) · y) · z ≡ (x · y) · z
{-# ATP prove lemma-4a #-}

postulate lemma-4b : ∀ x y z → (x · (y · (z · z))) ≡ x · (y · z)
{-# ATP prove lemma-4b #-}
