------------------------------------------------------------------------------
-- Lists examples
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Data.List.Examples where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Data.Nat.UnaryNumbers
open import Interactive.FOTC.Data.List.Type

------------------------------------------------------------------------------

l₁ : List (true ∷ false ∷ [])
l₁ = lcons true (lcons false lnil)

l₂ : List (zero ∷ 1' ∷ 2' ∷ [])
l₂ = lcons zero (lcons 1' (lcons 2' lnil))
