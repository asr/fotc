{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LogicalFramework.UniversalQuantifier where

postulate D : Set

-- The universal quantifier type on D.
data ForAll (A : D → Set) : Set where
  dfun : ((t : D) → A t) → ForAll A

dapp : {A : D → Set}(t : D) → ForAll A → A t
dapp t (dfun f) = f t
