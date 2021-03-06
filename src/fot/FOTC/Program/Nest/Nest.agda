------------------------------------------------------------------------------
-- Simple example of a nested recursive function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. Vol. 2152 of LNCS. 2001.

module FOTC.Program.Nest.Nest where

open import FOTC.Base

------------------------------------------------------------------------------
-- The nest function.
postulate
  nest   : D → D
  nest-0 : nest zero            ≡ zero
  nest-S : ∀ n → nest (succ₁ n) ≡ nest (nest n)
{-# ATP axioms nest-0 nest-S #-}
