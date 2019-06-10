------------------------------------------------------------------------------
-- Streams (unbounded lists)
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.Stream where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.Stream.Type public

------------------------------------------------------------------------------

postulate
  zeros    : D
  zeros-eq : zeros ≡ zero ∷ zeros
{-# ATP axiom zeros-eq #-}

postulate
  ones    : D
  ones-eq : ones ≡ succ₁ zero ∷ ones
{-# ATP axiom ones-eq #-}
