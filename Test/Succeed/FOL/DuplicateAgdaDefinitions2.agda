------------------------------------------------------------------------------
-- Testing the erasing of the duplicate definitions required by a conjecture
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.FOL.DuplicateAgdaDefinitions2 where

-- We add 4 to the fixities of the standard library.
infix 8 _<_ _≤_
infix 7 _≡_

------------------------------------------------------------------------------

postulate
  D               : Set
  zero true false : D
  succ            : D → D

data _≡_ (x : D) : D → Set where
  refl : x ≡ x

data N : D → Set where
  zN :               N zero
  sN : ∀ {n} → N n → N (succ n)

data Bool : D → Set where
  tB : Bool true
  fB : Bool false
{-# ATP axiom tB fB #-}

postulate
  _<_  : D → D → D
  <-00 :         zero   < zero   ≡ false
  <-0S : ∀ n →   zero   < succ n ≡ true
  <-S0 : ∀ n →   succ n < zero   ≡ false
  <-SS : ∀ m n → succ m < succ n ≡ m < n

_≤_ : D → D → D
m ≤ n = m < succ n
{-# ATP definition _≤_ #-}

NLE : D → D → Set
NLE m n = m ≤ n ≡ false
{-# ATP definition NLE #-}

postulate Sx≰0 : ∀ {n} → N n → NLE (succ n) zero

≤-Bool : ∀ {m n} → N m → N n → Bool (m ≤ n)
≤-Bool {n = n} zN Nn = prf
  where postulate prf : Bool (zero ≤ n)
≤-Bool (sN {m} Nm) zN = prf
  where postulate prf : Bool (succ m ≤ zero)
        {-# ATP prove prf Sx≰0 #-}
≤-Bool (sN {m} Nm) (sN {n} Nn) = prf (≤-Bool Nm Nn)
  where postulate prf : Bool (m ≤ n) → Bool (succ m ≤ succ n)
