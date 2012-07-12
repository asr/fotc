------------------------------------------------------------------------------
-- Testing the translation of definitions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Definition10 where

infixl 6 _+_
infix  4 _≡_

postulate
  D      : Set
  zero   : D
  succ   : D → D
  _≡_    : D → D → Set

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
  +-0x : ∀ n →   zero   + n ≡ n
  +-Sx : ∀ m n → succ m + n ≡ succ (m + n)
{-# ATP axiom +-0x +-Sx #-}

-- We test the translation of a definition where we need to erase
-- proof terms.
+-assoc : ∀ {m n o} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} Nm Nn No = N-ind A A0 is Nm
  where
  A : D → Set
  A i = i + n + o ≡ i + (n + o)
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 #-}

  postulate is : ∀ {i} → A i → A (succ i)
  {-# ATP prove is #-}
