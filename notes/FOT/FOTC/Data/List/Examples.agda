------------------------------------------------------------------------------
-- Lists examples
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Data.List.Examples where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.List.Type

------------------------------------------------------------------------------

l₁ : List (true ∷ false ∷ [])
l₁ = lcons true (lcons false lnil)

l₂ : List (zero ∷ 1' ∷ 2' ∷ [])
l₂ = lcons zero (lcons 1' (lcons 2' lnil))
