-- Tested with Agda 2.3.1 on 15 December 2011.

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Empty where

postulate
  ⊥      : Set
  ⊥-elim : {A : Set} → ⊥ → A
