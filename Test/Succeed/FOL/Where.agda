------------------------------------------------------------------------------
-- Testing the conjectures inside a where clause
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.FOL.Where where

infixl 6 _+_
infix  4 _≡_

postulate
  D      : Set
  zero   : D
  succ   : D → D
  _≡_    : D → D → Set

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

postulate
  _+_  : D → D → D
  +-x0 : ∀ d →   d + zero   ≡ d
  +-xS : ∀ d e → d + succ e ≡ succ (d + e)
{-# ATP axiom +-x0 #-}
{-# ATP axiom +-xS #-}

-- Left identify for addition using the induction principle for N and
-- calling the ATP for the base case and the induction step.
+-leftIdentity : ∀ {n} → N n → zero + n ≡ n
+-leftIdentity = indN P P0 iStep
  where
  P : D → Set
  P i = zero + i ≡ i

  postulate P0 : zero + zero ≡ zero
  {-# ATP prove P0 #-}

  postulate iStep : ∀ {i} → N i → zero + i ≡ i → zero + succ i ≡ succ i
  {-# ATP prove iStep #-}

------------------------------------------------------------------------------
-- Associativity of addition using the induction principle for N and
-- calling the ATP for the base case and the induction step.
+-assoc : ∀ {m n o} → N m → N n → N o → (m + n) + o ≡ m + (n + o)
+-assoc {m} {n} Nm Nn No = indN P P0 iStep No
  where
  P : D → Set
  P i = m + n + i ≡ m + (n + i)

  postulate P0 : m + n + zero ≡ m + (n + zero)
  {-# ATP prove P0 #-}

  postulate
    iStep : ∀ {i} → N i →
            m + n + i ≡ m + (n + i) → -- IH.
            m + n + succ i ≡ m + (n + succ i)
  {-# ATP prove iStep #-}
