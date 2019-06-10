------------------------------------------------------------------------------
-- A partial function: iter₀
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.Iter0.Iter0 where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List

------------------------------------------------------------------------------

postulate
  iter₀    : D → D → D
  iter₀-eq : ∀ f n → iter₀ f n ≡
             (if (iszero₁ n) then [] else (n ∷ iter₀ f (f · n)))
{-# ATP axiom iter₀-eq #-}
