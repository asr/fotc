------------------------------------------------------------------------------
-- PCF terms properties
------------------------------------------------------------------------------

module LTC.Minimal.Properties where

open import LTC.Minimal
open import LTC.Data.N

------------------------------------------------------------------------------
-- Closure properties

pred-N : {n : D} → N n → N (pred n)
pred-N zN  = prf
  where
    postulate prf : N (pred zero)
    {-# ATP prove prf zN #-}

pred-N (sN {n} Nn) = prf
  where
    -- TODO: The postulate N (pred $ succ n) is not proved by the ATP.
    postulate prf : N (pred (succ n))
    {-# ATP prove prf #-}
  -- {-# ATP hint pred-N #-}
