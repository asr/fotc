{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module CombiningProofs.WhereTranslation where

open import FOTC.Base
open import FOTC.Data.Nat

-- See Issue https://github.com/asr/apia/issues/81 .
+-rightIdentityA : D → Set
+-rightIdentityA i = i + zero ≡ i
{-# ATP definition +-rightIdentityA #-}

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity Nn = N-ind +-rightIdentityA A0 is Nn
  where
  postulate A0 : +-rightIdentityA zero
  {-# ATP prove A0 #-}

  postulate is : ∀ {i} → +-rightIdentityA i → +-rightIdentityA (succ₁ i)
  {-# ATP prove is #-}

A' : ∀ {n} → (Nn : N n) → D → Set
A' Nn i = i + zero ≡ i
-- {-# ATP definition A' #-}

postulate A0' : ∀ {n} → (Nn : N n) → A' Nn zero
-- {-# ATP prove A0' #-}

postulate is' : ∀ {n} → (Nn : N n) → ∀ {i} → A' Nn i → A' Nn (succ₁ i)
-- {-# ATP prove is' #-}
