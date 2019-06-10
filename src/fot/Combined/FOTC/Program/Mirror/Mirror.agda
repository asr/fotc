------------------------------------------------------------------------------
-- The mirror function: A function with higher-order recursion
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.Mirror.Mirror where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.List
open import Combined.FOTC.Program.Mirror.Type

------------------------------------------------------------------------------
-- The mirror function.
postulate
  mirror    : D
  mirror-eq : ∀ d ts → mirror · node d ts ≡ node d (reverse (map mirror ts))
{-# ATP axiom mirror-eq #-}
