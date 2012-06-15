{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Universal where

postulate D : Set

-- The universal quantifier type on D.
data Forall (A : D → Set) : Set where
  Forall-intro : ((t : D) → A t) → Forall A

Forall-elim : {A : D → Set} → Forall A → (t : D) → A t
Forall-elim (Forall-intro h) t = h t
