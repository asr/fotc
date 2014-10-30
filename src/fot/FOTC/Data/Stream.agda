------------------------------------------------------------------------------
-- Streams (unbounded lists)
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Stream where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream.Type public

------------------------------------------------------------------------------

postulate
  zeros    : D
  zeros-eq : zeros ≡ zero ∷ zeros
{-# ATP axiom zeros-eq #-}

postulate
  ones    : D
  ones-eq : ones ≡ succ₁ zero ∷ ones
{-# ATP axiom ones-eq #-}
