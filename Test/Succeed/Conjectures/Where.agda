------------------------------------------------------------------------------
-- Testing the conjectures inside a where clause
------------------------------------------------------------------------------

-- TODO: Two conjectures with the *same name* inside two different where
-- clauses should be generate two different TPTP files.

module Test.Succeed.Conjectures.Where where

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
  _+_    : D → D → D
  add-x0 : (d : D) → d + zero     ≡ d
  add-xS : (d e : D) → d + succ e ≡ succ (d + e)

{-# ATP axiom add-x0 #-}
{-# ATP axiom add-xS #-}

-- Left identify for addition using the induction principle for N and
-- calling the ATP for the base case and the induction step.
+-leftIdentity : {n : D} → N n → zero + n ≡ n
+-leftIdentity {n} = indN P P0 iStep
    where
      P : D → Set
      P i = zero + i ≡ i

      postulate
        P0 : zero + zero ≡ zero
      {-# ATP prove P0 #-}

      postulate
        iStep : {i : D} → N i → zero + i ≡ i → -- IH.
                zero + (succ i) ≡ succ i
      {-# ATP prove iStep #-}

------------------------------------------------------------------------------
-- Associativity of addition using the induction principle for N and
-- calling the ATP for the base case and the induction step.
+-assoc : {m n o : D} → N m → N n → N o → (m + n) + o ≡ m + (n + o)
+-assoc {m} {n} {o} Nm Nn No = indN P P0 iStep No
  where
    P : D → Set
    P i = m + n + i ≡ m + (n + i)

    postulate
      P0 : m + n + zero ≡ m + (n + zero)
    {-# ATP prove P0 #-}

    postulate
      iStep : {i : D} → N i →
              m + n + i ≡ m + (n + i) → -- IH.
              m + n + succ i ≡ m + (n + succ i)
    {-# ATP prove iStep #-}
