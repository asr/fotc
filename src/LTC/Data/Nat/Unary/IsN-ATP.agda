------------------------------------------------------------------------------
-- The unary numbers are LTC natural numbers
------------------------------------------------------------------------------

module LTC.Data.Nat.Unary.IsN-ATP where

open import LTC.Base

open import LTC.Data.Nat.Type
open import LTC.Data.Nat.Unary.Numbers

------------------------------------------------------------------------------

postulate
  N0 : N zero
  N1  : N one
  N10 : N ten
{-# ATP prove N1 #-}
{-# ATP prove N10 #-}

postulate
  N11 : N eleven
{-# ATP prove N11 #-}

postulate
  N89 : N eighty-nine
  N90 : N ninety
{-# ATP prove N89 #-}
{-# ATP prove N90 #-}

postulate
  N91  : N ninety-one
  N100 : N one-hundred
{-# ATP prove N91 #-}
{-# ATP prove N100 #-}

postulate
  N101 : N hundred-one
  N111 : N hundred-eleven
{-# ATP prove N101 #-}
{-# ATP prove N111 #-}
