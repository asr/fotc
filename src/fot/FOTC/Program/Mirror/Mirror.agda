------------------------------------------------------------------------------
-- The mirror function: A function with higher-order recursion
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.Mirror.Mirror where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------
-- The mirror function.
postulate
  mirror    : D
  mirror-eq : ∀ d ts → mirror · node d ts ≡ node d (reverse (map mirror ts))
{-# ATP axiom mirror-eq #-}
