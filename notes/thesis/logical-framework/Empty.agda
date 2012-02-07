-- Tested with the development version of Agda on 07 February 2012.

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Empty where

postulate
  ⊥      : Set
  ⊥-elim : {A : Set} → ⊥ → A
