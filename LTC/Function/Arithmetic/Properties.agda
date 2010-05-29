------------------------------------------------------------------------------
-- Arithmetic properties on total natural numbers
------------------------------------------------------------------------------

module LTC.Function.Arithmetic.Properties where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Function.Arithmetic

open import MyStdLib.Function

------------------------------------------------------------------------------
-- Closure properties

minus-N : {m n : D} → N m → N n → N (m - n)
minus-N {m} Nm zN = prf
  where
    postulate prf : N (m - zero)
    {-# ATP prove prf #-}

minus-N zN (sN {n} Nn) = prf
  where
    postulate prf : N (zero - succ n)
    {-# ATP prove prf zN #-}

minus-N (sN {m} Nm) (sN {n} Nn) = prf $ minus-N Nm Nn
  where
    postulate prf : N (m - n) → N (succ m - succ n)
    {-# ATP prove prf #-}

+-N : {m n : D} → N m → N n → N (m + n)
+-N {n = n} zN Nn = prf
  where
    postulate prf : N (zero + n)
    {-# ATP prove prf #-}
+-N {n = n} (sN {m} Nm ) Nn = prf (+-N Nm Nn)
  where
    postulate prf : N (m + n) → N (succ m + n)
    {-# ATP prove prf sN #-}

*-N : {m n : D} → N m → N n → N (m * n)
*-N {n = n} zN Nn = prf
  where
    postulate prf : N (zero * n)
    {-# ATP prove prf zN #-}
*-N {n = n} (sN {m} Nm) Nn = prf (*-N Nm Nn)
  where
    postulate prf : N (m * n) → N (succ m * n)
    {-# ATP prove prf +-N #-}

------------------------------------------------------------------------------

-- Some proofs are based on the proofs in the standard library

+-leftIdentity : {n : D} → N n → zero + n ≡ n
+-leftIdentity {n} _ = +-0x n

+-rightIdentity : {n : D} → N n → n + zero ≡ n
+-rightIdentity zN          = +-leftIdentity zN
+-rightIdentity (sN {n} Nn) = prf $ +-rightIdentity Nn
   where
     postulate prf : n + zero ≡ n → succ n + zero ≡ succ n
     {-# ATP prove prf #-}

+-assoc : {m n o : D} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o = o} zN Nn No = prf
  where
    postulate prf : zero + n + o ≡ zero + (n + o)
    {-# ATP prove prf #-}
+-assoc {n = n} {o = o} (sN {m} Nm) Nn No = prf $ +-assoc Nm Nn No
  where
    postulate prf : m + n + o ≡ m + (n + o) →
                    succ m + n + o ≡ succ m + (n + o)
    {-# ATP prove prf #-}

x+1+y≡1+x+y : {m n : D} → N m → N n → m + succ n ≡ succ (m + n)
x+1+y≡1+x+y {n = n} zN Nn = prf
  where
    postulate prf : zero + succ n ≡ succ (zero + n)
    {-# ATP prove prf #-}
x+1+y≡1+x+y {n = n} (sN {m} Nm) Nn = prf (x+1+y≡1+x+y Nm Nn)
  where
    postulate prf : m + succ n ≡ succ (m + n) →
                    succ m + succ n ≡ succ (succ m + n)
    {-# ATP prove prf #-}

+-comm : {m n : D} → N m → N n → m + n ≡ n + m
+-comm {n = n} zN Nn = prf
  where
    postulate prf : zero + n ≡ n + zero
    {-# ATP prove prf +-rightIdentity #-}
+-comm {n = n} (sN {m} Nm) Nn = prf (+-comm Nm Nn)
  where
    postulate prf : m + n ≡ n + m → succ m + n ≡ n + succ m
    {-# ATP prove prf x+1+y≡1+x+y #-}

minus-0x : {n : D} → N n → zero - n  ≡ zero
minus-0x zN          = minus-x0 zero
minus-0x (sN {n} Nn) = minus-0S n

[x+y]-[x+z]≡y-z : {m n o : D} → N m → N n → N o →
                  (m + n) - (m + o) ≡ n - o
[x+y]-[x+z]≡y-z {n = n} {o = o} zN Nn No = prf
  where
    postulate prf : (zero + n) - (zero + o) ≡ n - o
    {-# ATP prove prf #-}

-- Nice proof by the ATP.
[x+y]-[x+z]≡y-z {n = n} {o = o} (sN {m} Nm) Nn No =
  prf ([x+y]-[x+z]≡y-z Nm Nn No)
  where
    postulate prf : (m + n) - (m + o) ≡ n - o →
                    (succ m + n) - (succ m + o) ≡ n - o
    {-# ATP prove prf #-}

*-leftZero : {n : D} → N n → zero * n ≡ zero
*-leftZero {n} _ = *-0x n

*-rightZero : {n : D} → N n → n * zero ≡ zero
*-rightZero zN          = *-leftZero zN
*-rightZero (sN {n} Nn) = prf (*-rightZero Nn)
  where
    postulate prf : n * zero ≡ zero → succ n * zero ≡ zero
    {-# ATP prove prf #-}

postulate *-leftIdentity : {n : D} → N n → succ zero * n ≡ n
{-# ATP prove *-leftIdentity +-rightIdentity #-}

x*1+y≡x+xy : {m n : D} → N m → N n → m * succ n ≡ m + m * n
x*1+y≡x+xy {n = n} zN Nn = prf
  where
    postulate prf : zero * succ n ≡ zero + zero * n
    {-# ATP prove prf #-}
x*1+y≡x+xy {n = n} (sN {m} Nm) Nn = prf (x*1+y≡x+xy Nm Nn)
                                        (+-assoc Nn Nm (*-N Nm Nn))
                                        (+-assoc Nm Nn (*-N Nm Nn))
  where
    -- N.B. We had to feed the ATP with the instances of the associate law
    postulate prf :  m * succ n ≡ m + m * n → -- IH
                     (n + m) + (m * n) ≡ n + (m + (m * n)) → -- Associative law
                     (m + n) + (m * n) ≡ m + (n + (m * n)) → -- Associateve law
                     succ m * succ n ≡ succ m + succ m * n
    {-# ATP prove prf +-comm #-}

*-comm : {m n : D} → N m → N n → m * n ≡ n * m
*-comm {n = n} zN Nn = prf
  where
    postulate prf : zero * n ≡ n * zero
    {-# ATP prove prf *-rightZero #-}
*-comm {n = n} (sN {m} Nm) Nn = prf (*-comm Nm Nn)
  where
    postulate prf : m * n ≡ n * m →
                    succ m * n ≡ n * succ m
    {-# ATP prove prf x*1+y≡x+xy #-}

[x-y]z≡xz*yz : {m n o : D} → N m → N n → N o → (m - n) * o ≡ m * o - n * o
[x-y]z≡xz*yz {m} .{zero} {o} Nm zN No = prf
  where
    postulate prf : (m - zero) * o ≡ m * o - zero * o
    {-# ATP prove prf #-}

[x-y]z≡xz*yz {o = o} zN (sN {n} Nn) No = prf (minus-0x (*-N (sN Nn) No))
  where
    postulate prf : zero - succ n * o ≡ zero →
                    (zero - succ n) * o ≡ zero * o - succ n * o
    {-# ATP prove prf #-}

[x-y]z≡xz*yz (sN {m} Nm) (sN {n} Nn) zN = prf
  where
    postulate prf : (succ m - succ n) * zero ≡ succ m * zero - succ n * zero
    {-# ATP prove prf *-comm minus-N zN #-}

[x-y]z≡xz*yz (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  prf ([x-y]z≡xz*yz Nm Nn (sN No))
  where
    postulate prf : (m - n) * succ o ≡ m * succ o - n * succ o → -- IH
                    (succ m - succ n) * succ o ≡
                    succ m * succ o - succ n * succ o
    {-# ATP prove prf sN *-N [x+y]-[x+z]≡y-z #-}

[x+y]z≡xz*yz : {m n o : D} → N m → N n → N o → (m + n) * o ≡ m * o + n * o
[x+y]z≡xz*yz {m} {n} Nm Nn zN = prf
  where
    postulate prf : (m + n) * zero ≡ m * zero + n * zero
    {-# ATP prove prf zN sN *-comm +-rightIdentity *-N +-N #-}

[x+y]z≡xz*yz {n = n} zN Nn (sN {o} No) = prf
  where
    postulate prf :  (zero + n) * succ o ≡ zero * succ o + n * succ o
    {-# ATP prove prf #-}

[x+y]z≡xz*yz (sN {m} Nm) zN (sN {o} No) = prf
  where
    postulate prf : (succ m + zero) * succ o ≡ succ m * succ o + zero * succ o
    {-# ATP prove prf +-rightIdentity *-leftZero sN *-N #-}

[x+y]z≡xz*yz (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  prf ([x+y]z≡xz*yz Nm (sN Nn) (sN No))
    where
      postulate
        prf : (m + succ n) * succ o ≡ m * succ o + succ n * succ o →
              (succ m + succ n) * succ o ≡ succ m * succ o + succ n * succ o
      {-# ATP prove prf +-assoc sN *-N #-}
