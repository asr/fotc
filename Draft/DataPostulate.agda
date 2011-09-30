------------------------------------------------------------------------------
-- Data and postulates
------------------------------------------------------------------------------

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

indN : (P : D → Set) →
       P zero →
       (∀ {n} → N n → P n → P (succ n)) →
       ∀ {n} → N n → P n
indN P P0 h zN      = P0
indN P P0 h (sN Nn) = h Nn (indN P P0 h Nn)

-- The FOTC natural numbers using postulates (we choose 'M' by 'Model').
postulate
  M    : D → Set
  zM   : M zero
  sM   : ∀ {n} → M n → M (succ n)
  indM : (P : D → Set) →
         P zero →
         (∀ {n} → M n → P n → P (succ n)) →
         ∀ {n} → M n → P n

------------------------------------------------------------------------------
-- From data to postulates

-- The predicate: Using the induction principle.
nat-D2P : ∀ {n} → N n → M n
nat-D2P = indN M zM (λ _ Mn → sM Mn)

-- The predicate: Using pattern matching.
nat-D2P' : ∀ {n} → N n → M n
nat-D2P' zN      = zM
nat-D2P' (sN Nn) = sM (nat-D2P' Nn)

------------------------------------------------------------------------------
-- From postulates to data

-- The predicate.
nat-P2D : ∀ {n} → M n → N n
nat-P2D = indM N zN (λ _ Nn → sN Nn)
