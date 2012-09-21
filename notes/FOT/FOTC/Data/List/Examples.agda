------------------------------------------------------------------------------
-- Lists examples
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.List.Examples where

open import FOTC.Base
open FOTC.Base.BList
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.List.Type

------------------------------------------------------------------------------

l₁ : List (true ∷ false ∷ [])
l₁ = lcons true (lcons false lnil)

l₂ : List (zero ∷ one ∷ two ∷ [])
l₂ = lcons zero (lcons one (lcons two lnil))
