module Test.Succeed.DefinitionsInsideWhereClauses where

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
  sN : {n : D} → N n → N (succ n)

-- Induction principle for N (elimination rule).
indN : (P : D → Set) →
       P zero →
       ({n : D} → N n → P n → P (succ n)) →
       {n : D} → N n → P n
indN P p0 h zN      = p0
indN P p0 h (sN Nn) = h Nn (indN P p0 h Nn)

postulate
  _+_  : D → D → D
  +-0x : (d : D) → zero + d     ≡ d
  +-Sx : (d e : D) → succ d + e ≡ succ (d + e)
{-# ATP axiom +-0x #-}
{-# ATP axiom +-Sx #-}

+-rightIdentity : {n : D} → N n → n + zero ≡ n
+-rightIdentity {n} Nn = indN P P0 iStep Nn
  where
    P : D → Set
    P i = i + zero ≡ i
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 #-}

    postulate
      iStep : {i : D} → N i → P i → P (succ i)
    {-# ATP prove iStep #-}

+-assoc : {m n o : D} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {m} {n} {o} Nm Nn No = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + n + o ≡ i + (n + o)
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 #-}

    postulate
      iStep : {i : D} → N i → P i → P (succ i)
    {-# ATP prove iStep #-}
