------------------------------------------------------------------------------
-- Arithmetic properties on total natural numbers
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Properties where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC-PCF.Data.Nat
  using ( _+_ ; _-_ ; _*_
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.Data.Nat.Rec.Equations using ( rec-0 ; rec-S )

------------------------------------------------------------------------------

postulate
  +-0x : (d : D) → zero + d ≡ d
{-# ATP prove +-0x rec-0 #-}

postulate
  +-Sx : (d e : D) → succ d + e ≡ succ (d + e)
{-# ATP prove +-Sx rec-S #-}

postulate
  minus-x0 : (d : D) → d - zero ≡ d
{-# ATP prove minus-x0 rec-0 #-}

minus-0S : {n : D} → N n → zero - succ n ≡ zero
minus-0S zN = prf
  where
    postulate prf : zero - succ zero ≡ zero
    {-# ATP prove prf rec-0 #-}

minus-0S (sN {n} _) = prf
  where
    postulate prf : zero - succ (succ n) ≡ zero
    {-# ATP prove prf rec-S minus-0S #-}

minus-0x : {n : D} → N n → zero - n ≡ zero
minus-0x zN      = minus-x0 zero
minus-0x (sN Nn) = minus-0S Nn

minus-SS : {m n : D} → N m → N n → succ m - succ n ≡ m - n
minus-SS {m} _ zN = prf
  where
    postulate prf : succ m - succ zero ≡ m - zero
    -- Equinox 5.0alpha (2010-06-29) no-success due to timeout (180 sec).
    {-# ATP prove prf rec-S minus-x0 #-}

minus-SS zN (sN {n} Nn) = prf $ minus-SS zN Nn
  where
    postulate prf : succ zero - succ n ≡ zero - n →  -- IH.
                    succ zero - succ (succ n) ≡ zero - succ n
    {-# ATP prove prf rec-S minus-0x minus-0S #-}

minus-SS (sN {m} Nm) (sN {n} Nn) = prf $ minus-SS (sN Nm) Nn
  where
    postulate prf : succ (succ m) - succ n ≡ succ m - n →  -- IH.
                    succ (succ m) - succ (succ n) ≡ succ m - succ n
    {-# ATP prove prf rec-S #-}

postulate
  *-0x : (d : D) → zero * d ≡ zero
{-# ATP prove *-0x rec-0 #-}

postulate
  *-Sx : (d e : D) → succ d * e ≡ e + (d * e)
{-# ATP prove *-Sx rec-S #-}

------------------------------------------------------------------------------
-- Closure properties

minus-N : {m n : D} → N m → N n → N (m - n)
minus-N {m} _ zN = prf
  where
    postulate prf : N (m - zero)
    {-# ATP prove prf minus-x0 #-}

minus-N zN (sN {n} _) = prf
  where
    postulate prf : N (zero - succ n)
    {-# ATP prove prf zN minus-0S #-}

minus-N (sN {m} Nm) (sN {n} Nn) = prf $ minus-N Nm Nn
  where
    postulate prf : N (m - n) →  -- IH.
                    N (succ m - succ n)
    {-# ATP prove prf minus-SS #-}

+-N : {m n : D} → N m → N n → N (m + n)
+-N {n = n} zN _ = prf
  where
    postulate prf : N (zero + n)
    {-# ATP prove prf +-0x #-}
+-N {n = n} (sN {m} Nm) Nn = prf $ +-N Nm Nn
  where
    postulate prf : N (m + n) →  -- IH.
                    N (succ m + n)
    {-# ATP prove prf sN +-Sx #-}

*-N : {m n : D} → N m → N n → N (m * n)
*-N {n = n} zN Nn = prf
  where
    postulate prf : N (zero * n)
    {-# ATP prove prf zN *-0x #-}
*-N {n = n} (sN {m} Nm) Nn = prf $ *-N Nm Nn
  where
    postulate prf : N (m * n) →  -- IH.
                    N (succ m * n)
    {-# ATP prove prf +-N *-Sx #-}

------------------------------------------------------------------------------
-- Some proofs are based on the proofs in the standard library.

+-leftIdentity : {n : D} → N n → zero + n ≡ n
+-leftIdentity {n} _ = +-0x n

+-rightIdentity : {n : D} → N n → n + zero ≡ n
+-rightIdentity zN          = +-leftIdentity zN
+-rightIdentity (sN {n} Nn) = prf $ +-rightIdentity Nn
   where
     postulate prf : n + zero ≡ n →  -- IH.
                     succ n + zero ≡ succ n
     {-# ATP prove prf +-Sx #-}

+-assoc : {m n o : D} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} zN _ _ = prf
  where
    postulate prf : zero + n + o ≡ zero + (n + o)
    {-# ATP prove prf +-0x #-}
+-assoc {n = n} {o} (sN {m} Nm) Nn No = prf $ +-assoc Nm Nn No
  where
    postulate prf : m + n + o ≡ m + (n + o) →  -- IH.
                    succ m + n + o ≡ succ m + (n + o)
    {-# ATP prove prf +-Sx #-}

x+1+y≡1+x+y : {m n : D} → N m → N n → m + succ n ≡ succ (m + n)
x+1+y≡1+x+y {n = n} zN _ = prf
  where
    postulate prf : zero + succ n ≡ succ (zero + n)
    {-# ATP prove prf +-0x #-}
x+1+y≡1+x+y {n = n} (sN {m} Nm) Nn = prf $ x+1+y≡1+x+y Nm Nn
  where
    postulate prf : m + succ n ≡ succ (m + n) →  -- IH.
                    succ m + succ n ≡ succ (succ m + n)
    {-# ATP prove prf +-Sx #-}

+-comm : {m n : D} → N m → N n → m + n ≡ n + m
+-comm {n = n} zN _ = prf
  where
    postulate prf : zero + n ≡ n + zero
    {-# ATP prove prf +-rightIdentity +-0x #-}
+-comm {n = n} (sN {m} Nm) Nn = prf $ +-comm Nm Nn
  where
    postulate prf : m + n ≡ n + m →  -- IH.
                    succ m + n ≡ n + succ m
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf x+1+y≡1+x+y +-Sx #-}

[x+y]-[x+z]≡y-z : {m n o : D} → N m → N n → N o →
                  (m + n) - (m + o) ≡ n - o
[x+y]-[x+z]≡y-z {n = n} {o} zN _ _ = prf
  where
    postulate prf : (zero + n) - (zero + o) ≡ n - o
    {-# ATP prove prf +-0x #-}

-- Nice proof by the ATP.
[x+y]-[x+z]≡y-z {n = n} {o} (sN {m} Nm) Nn No =
  prf $ [x+y]-[x+z]≡y-z Nm Nn No
  where
    postulate prf : (m + n) - (m + o) ≡ n - o →  -- IH.
                    (succ m + n) - (succ m + o) ≡ n - o
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf +-Sx minus-SS +-N #-}

*-leftZero : (n : D) → zero * n ≡ zero
*-leftZero = *-0x

*-rightZero : {n : D} → N n → n * zero ≡ zero
*-rightZero zN          = *-leftZero zero
*-rightZero (sN {n} Nn) = prf $ *-rightZero Nn
  where
    postulate prf : n * zero ≡ zero →  -- IH.
                    succ n * zero ≡ zero
    {-# ATP prove prf +-0x *-Sx #-}

postulate *-leftIdentity : {n : D} → N n → succ zero * n ≡ n
{-# ATP prove *-leftIdentity +-rightIdentity *-0x *-Sx #-}

x*1+y≡x+xy : {m n : D} → N m → N n → m * succ n ≡ m + m * n
x*1+y≡x+xy {n = n} zN _ = prf
  where
    postulate prf : zero * succ n ≡ zero + zero * n
    {-# ATP prove prf +-0x *-0x #-}
x*1+y≡x+xy {n = n} (sN {m} Nm) Nn = prf (x*1+y≡x+xy Nm Nn)
                                        (+-assoc Nn Nm (*-N Nm Nn))
                                        (+-assoc Nm Nn (*-N Nm Nn))
  where
    -- N.B. We had to feed the ATP with the instances of the associate law
    postulate prf :  m * succ n ≡ m + m * n →  -- IH
                     (n + m) + (m * n) ≡ n + (m + (m * n)) →  -- Associative law
                     (m + n) + (m * n) ≡ m + (n + (m * n)) →  -- Associateve law
                     succ m * succ n ≡ succ m + succ m * n
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf +-comm +-Sx *-Sx #-}

*-comm : {m n : D} → N m → N n → m * n ≡ n * m
*-comm {n = n} zN _ = prf
  where
    postulate prf : zero * n ≡ n * zero
    {-# ATP prove prf *-rightZero *-0x #-}
*-comm {n = n} (sN {m} Nm) Nn = prf $ *-comm Nm Nn
  where
    postulate prf : m * n ≡ n * m →  -- IH.
                    succ m * n ≡ n * succ m
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf x*1+y≡x+xy *-Sx #-}

[x-y]z≡xz*yz : {m n o : D} → N m → N n → N o → (m - n) * o ≡ m * o - n * o
[x-y]z≡xz*yz {m} {o = o} _ zN _ = prf
  where
    postulate prf : (m - zero) * o ≡ m * o - zero * o
    {-# ATP prove prf *-0x minus-x0 #-}

[x-y]z≡xz*yz {o = o} zN (sN {n} Nn) No = prf $ minus-0x (*-N (sN Nn) No)
  where
    postulate prf : zero - succ n * o ≡ zero →
                    (zero - succ n) * o ≡ zero * o - succ n * o
    {-# ATP prove prf *-0x minus-0S minus-0x #-}

[x-y]z≡xz*yz (sN {m} _) (sN {n} _) zN = prf
  where
    postulate prf : (succ m - succ n) * zero ≡ succ m * zero - succ n * zero
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf *-comm minus-N zN sN +-0x *-0x *-Sx minus-0x *-N #-}

[x-y]z≡xz*yz (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  prf $ [x-y]z≡xz*yz Nm Nn (sN No)
  where
    postulate prf : (m - n) * succ o ≡ m * succ o - n * succ o →  -- IH
                    (succ m - succ n) * succ o ≡
                    succ m * succ o - succ n * succ o
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf sN *-N [x+y]-[x+z]≡y-z *-Sx minus-SS #-}

[x+y]z≡xz*yz : {m n o : D} → N m → N n → N o → (m + n) * o ≡ m * o + n * o
[x+y]z≡xz*yz {m} {n} _ _ zN = prf
  where
    postulate prf : (m + n) * zero ≡ m * zero + n * zero
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf zN sN *-comm +-rightIdentity *-N +-N *-0x #-}

[x+y]z≡xz*yz {n = n} zN Nn (sN {o} _) = prf
  where
    postulate prf :  (zero + n) * succ o ≡ zero * succ o + n * succ o
    {-# ATP prove prf +-0x *-0x #-}

[x+y]z≡xz*yz (sN {m} _) zN (sN {o} _) = prf
  where
    postulate prf : (succ m + zero) * succ o ≡ succ m * succ o + zero * succ o
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf +-rightIdentity *-leftZero sN *-N #-}

[x+y]z≡xz*yz (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  prf $ [x+y]z≡xz*yz Nm (sN Nn) (sN No)
    where
      postulate
        prf : (m + succ n) * succ o ≡ m * succ o + succ n * succ o →  -- IH.
              (succ m + succ n) * succ o ≡ succ m * succ o + succ n * succ o
      -- E 1.2 cannot no-success due to timeout (180 sec).
      -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
      {-# ATP prove prf +-assoc sN *-N +-Sx *-Sx #-}
