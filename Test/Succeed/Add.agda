module Test.Succeed.Add where

infixl 6 _+_
infix  4 _≡_

postulate
  D      : Set
  zero   : D
  succ   : D → D

-- The LTC natural numbers type.
data N : D → Set where
  zN : N zero
  sN : ∀ {n} → N n → N (succ n)

-- Induction principle for N (elimination rule).
indN : (P : D → Set) →
       P zero →
       (∀ {n} → N n → P n → P (succ n)) →
       ∀ {n} → N n → P n
indN P P0 h zN      = P0
indN P P0 h (sN Nn) = h Nn (indN P P0 h Nn)

-- The identity type.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

postulate
  _+_  : D → D → D
  +-x0 : ∀ d →   d + zero   ≡ d
  +-xS : ∀ d e → d + succ e ≡ succ (d + e)
{-# ATP axiom +-x0 #-}
{-# ATP axiom +-xS #-}

-- Left identify for addition using the induction principle for N and
-- calling the ATP for the base case and the induction step.
+-leftIdentity : ∀ {n} → N n → zero + n ≡ n
+-leftIdentity {n} = indN P P0 iStep
  where
  P : D → Set
  P i = zero + i ≡ i

  postulate P0 : zero + zero ≡ zero
  {-# ATP prove P0 #-}

  postulate iStep : ∀ {i} → N i → zero + i ≡ i → zero + succ i ≡ succ i
  {-# ATP prove iStep #-}
