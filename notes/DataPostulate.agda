------------------------------------------------------------------------------
-- Data and postulates
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Are the FOTC natural numbers defined by data and postulates the
-- same?

module DataPostulate where

------------------------------------------------------------------------------
postulate
  D    : Set
  zero : D
  succ : D → D

-- The FOTC natural numbers using data.
data N : D → Set where
  zN :               N zero
  sN : ∀ {n} → N n → N (succ n)

N-ind : (P : D → Set) →
        P zero →
        (∀ {n} → N n → P n → P (succ n)) →
        ∀ {n} → N n → P n
N-ind P P0 h zN      = P0
N-ind P P0 h (sN Nn) = h Nn (N-ind P P0 h Nn)

-- The FOTC natural numbers using postulates (we chose 'M' by 'Model').
postulate
  M    : D → Set
  zM   : M zero
  sM   : ∀ {n} → M n → M (succ n)
  M-ind : (P : D → Set) →
          P zero →
          (∀ {n} → M n → P n → P (succ n)) →
          ∀ {n} → M n → P n

------------------------------------------------------------------------------
-- The predicates

-- From the data predicate to the postulated one: Using the induction
-- principle.
nat-D2P : ∀ {n} → N n → M n
nat-D2P = N-ind M zM (λ _ Mn → sM Mn)

-- From the data predicate to the postulated one: Using pattern
-- matching.
nat-D2P' : ∀ {n} → N n → M n
nat-D2P' zN      = zM
nat-D2P' (sN Nn) = sM (nat-D2P' Nn)

-- From the postulated predicate to the data one.
nat-P2D : ∀ {n} → M n → N n
nat-P2D = M-ind N zN (λ _ Nn → sN Nn)

------------------------------------------------------------------------------
-- The induction principles

-- The postulated inductive principle from the data one.
D2P-ind : (P : D → Set) → P zero →
          (∀ {n} → M n → P n → P (succ n)) →
          ∀ {n} → M n → P n
D2P-ind P P0 ih Mn = N-ind P P0 (λ {_} Nn → ih (nat-D2P Nn)) (nat-P2D Mn)

-- The data inductive principle from the postulated one.
P2D-ind : (P : D → Set) → P zero →
          (∀ {n} → N n → P n → P (succ n)) →
          ∀ {n} → N n → P n
P2D-ind P P0 ih Nn = M-ind P P0 (λ {_} Mn → ih (nat-P2D Mn)) (nat-D2P Nn)
