module Test.Fail.UsingPredicatesWithConjectures where

infixl 6 _+_
infix  4 _≡_

postulate
  D      : Set
  zero   : D
  succ   : D → D

-- The identity type.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- The LTC natural numbers type.
data N : D → Set where
  zN : N zero
  sN : {n : D} → N n → N (succ n)

-- Induction principle for N (elimination rule).
indN : (P : D → Set) →
       P zero →
       ({n : D} → N n → P n → P (succ n)) →
       {n : D} → N n → P n
indN P p0 h zN      = p0
indN P p0 h (sN Nn) = h Nn (indN P p0 h Nn)

postulate
  _+_    : D → D → D
  add-x0 : (n : D) → n + zero     ≡ n
  add-xS : (m n : D) → m + succ n ≡ succ (m + n)

{-# ATP axiom add-x0 #-}
{-# ATP axiom add-xS #-}

P : D → Set
P i = zero + i ≡ i

postulate
  P0₁ : zero + zero ≡ zero
{-# ATP prove P0₁ #-}

postulate
  iStep₁ : {i : D} → N i → zero + i ≡ i → zero + (succ i) ≡ succ i
{-# ATP prove iStep₁ #-}

addLeftIdentity₁ : {n : D} → N n → zero + n ≡ n
addLeftIdentity₁ = indN (λ i → P i) P0₁ iStep₁

-- Equinox cannot prove the postulates P0₂ and iStep₂ because he does
-- not the definition of the predicate P. It seems we should use the
-- TPTP definitions.
postulate
  P0₂ : P zero
-- {-# ATP prove P0₂ #-}

postulate
  iStep₂ : {i : D} → N i → P i → P (succ i)
-- {-# ATP prove iStep₂ #-}

addLeftIdentity₂ : {n : D} → N n → zero + n ≡ n
addLeftIdentity₂ = indN (λ i → P i) P0₂ iStep₂
