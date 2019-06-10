------------------------------------------------------------------------------
-- Exclusive disjunction base
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOL.ExclusiveDisjunction.Base where

open import Combined.FOL.Base

infixr 1 _⊻_

------------------------------------------------------------------------------
-- Exclusive disjunction.
_⊻_ : Set → Set → Set
P ⊻ Q = (P ∨ Q) ∧ ¬ (P ∧ Q)
