------------------------------------------------------------------------------
-- Simple example of a nested recursive function
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. Vol. 2152 of LNCS. 2001.

module FOT.FOTC.Program.Nest.NestConditional where

open import FOTC.Base

------------------------------------------------------------------------------
-- The nest function.
postulate
  nest    : D → D
  nest-eq : ∀ n → nest n ≡ (if (iszero₁ n)
                              then zero
                              else (nest (nest (pred₁ n))))
{-# ATP axiom nest-eq #-}
