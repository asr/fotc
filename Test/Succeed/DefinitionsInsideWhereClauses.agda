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
+-rightIdentity {n} Nn = indN Q Q0 iStep Nn
  where
    Q : D → Set
    Q i = i + zero ≡ i
    {-# ATP definition Q #-}

    postulate
      Q0 : Q zero
    {-# ATP prove Q0 #-}

    postulate
      iStep : {i : D} → N i → Q i → Q (succ i)
    {-# ATP prove iStep #-}
