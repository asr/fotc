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

-- Induction principle.
N-ind : (A : D → Set) →
       A zero →
       (∀ {n} → A n → A (succ n)) →
       ∀ {n} → N n → A n
N-ind A A0 h zN      = A0
N-ind A A0 h (sN Nn) = h (N-ind A A0 h Nn)

postulate
  _+_  : D → D → D
  +-x0 : ∀ n →   n + zero   ≡ n
  +-xS : ∀ m n → m + succ n ≡ succ (m + n)
{-# ATP axiom +-x0 +-xS #-}

-- Left identify for addition using the induction principle for N and
-- calling the ATP for the base case and the induction step.
+-leftIdentity : ∀ {n} → N n → zero + n ≡ n
+-leftIdentity = N-ind A A0 is
  where
  A : D → Set
  A i = zero + i ≡ i

  postulate A0 : zero + zero ≡ zero
  {-# ATP prove A0 #-}

  postulate is : ∀ {i} → zero + i ≡ i → zero + succ i ≡ succ i
  {-# ATP prove is #-}

------------------------------------------------------------------------------
-- Associativity of addition using the induction principle for N and
-- calling the ATP for the base case and the induction step.
+-assoc : ∀ {m n o} → N m → N n → N o → (m + n) + o ≡ m + (n + o)
+-assoc {m} {n} Nm Nn No = N-ind A A0 is No
  where
  A : D → Set
  A i = m + n + i ≡ m + (n + i)

  postulate A0 : m + n + zero ≡ m + (n + zero)
  {-# ATP prove A0 #-}

  postulate
    is : ∀ {i} →
         m + n + i ≡ m + (n + i) →
         m + n + succ i ≡ m + (n + succ i)
  {-# ATP prove is #-}
