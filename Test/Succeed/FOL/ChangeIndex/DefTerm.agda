------------------------------------------------------------------------------
-- Testing the class AgdaLib.DeBruijn.ChangeIndex: (Def _ []) term
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.FOL.ChangeIndex.DefTerm where

infixl 6 _+_
infix  4 _≡_

postulate
  D    : Set
  zero : D
  succ : D → D

-- The LTC natural numbers type.
data N : D → Set where
  zN : N zero
  sN : ∀ {n} → N n → N (succ n)

-- Induction principle for N (elimination rule).
N-ind : (A : D → Set) →
       A zero →
       (∀ {n} → A n → A (succ n)) →
       ∀ {n} → N n → A n
N-ind A A0 h zN      = A0
N-ind A A0 h (sN Nn) = h (N-ind A A0 h Nn)

-- The identity type.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

postulate
  _+_  : D → D → D
  +-0x : ∀ n →   zero   + n ≡ n
  +-Sx : ∀ m n → succ m + n ≡ succ (m + n)
{-# ATP axiom +-0x +-Sx #-}

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity Nn = N-ind A A0 is Nn
  where
  A : D → Set
  A i = i + zero ≡ i
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 #-}

  postulate is : ∀ {i} → A i → A (succ i)
  {-# ATP prove is #-}
