------------------------------------------------------------------------------
-- Example using distributive laws on a binary operation via Agsy
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas     #-}
{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Tested with the development version of the Agda standard library on
-- 02 February 2012.

module Agsy.DistributiveLaws.TaskB where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

infixl 7 _·_

------------------------------------------------------------------------------
-- Distributive laws axioms

postulate
  D   : Set        -- The universe
  _·_ : D → D → D  -- The binary operation.

  leftDistributive  : ∀ x y z → x · (y · z) ≡ (x · y) · (x · z)
  rightDistributive : ∀ x y z → (x · y) · z ≡ (x · z) · (y · z)

-- Properties

taskB : ∀ u x y z →
        (x · y · (z · u)) · ((x · y · ( z · u)) · (x · z · (y · u))) ≡
          x · z · (y · u)
taskB u x y z = {!-t 20 -m!}  -- Agsy fails
