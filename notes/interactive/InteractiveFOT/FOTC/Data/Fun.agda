------------------------------------------------------------------------------
-- An inductive predicate for representing functions
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Data.Fun where

open import Interactive.FOTC.Base

------------------------------------------------------------------------------
-- 2012-03-13. I don't see how we can distinguish between data
-- elements and functions in FOTC. The following inductive predicate
-- is true for any element d : D.
data Fun : D → Set where
  fun : (f : D) → Fun f

-- But using a λ-abstraction we could make a distinguish:
postulate lam : (D → D) → D  -- LTC-PCF λ-abstraction.

data Fun₁ : D → Set where
  fun₁ : (f : D → D) → Fun₁ (lam f)
