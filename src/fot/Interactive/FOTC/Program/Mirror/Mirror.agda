------------------------------------------------------------------------------
-- The mirror function: A function with higher-order recursion
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.Mirror.Mirror where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Program.Mirror.Type

------------------------------------------------------------------------------
-- The mirror function.
postulate
  mirror    : D
  mirror-eq : ∀ d ts → mirror · node d ts ≡ node d (reverse (map mirror ts))
