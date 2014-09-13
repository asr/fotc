{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module CombiningProofs.WhereTranslation where

open import FOTC.Base
open import FOTC.Data.Nat

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity Nn = N-ind A A0 is Nn
  where
  A : D → Set
  A i = i + zero ≡ i
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 #-}

  postulate is : ∀ {i} → A i → A (succ₁ i)
  {-# ATP prove is #-}

A' : ∀ {n} → (Nn : N n) → D → Set
A' Nn i = i + zero ≡ i
-- {-# ATP definition A' #-}

postulate A0' : ∀ {n} → (Nn : N n) → A' Nn zero
-- {-# ATP prove A0' #-}

postulate is' : ∀ {n} → (Nn : N n) → ∀ {i} → A' Nn i → A' Nn (succ₁ i)
-- {-# ATP prove is' #-}
