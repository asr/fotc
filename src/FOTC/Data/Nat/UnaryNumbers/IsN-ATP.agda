------------------------------------------------------------------------------
-- The unary numbers are FOTC natural numbers
------------------------------------------------------------------------------

module FOTC.Data.Nat.UnaryNumbers.IsN-ATP where

open import FOTC.Base

open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

postulate
  N0  : N zero
  N1  : N one
  N10 : N ten
{-# ATP prove N0 #-}
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
  N92  : N ninety-two
  N93  : N ninety-three
  N94  : N ninety-four
  N95  : N ninety-five
  N96  : N ninety-six
  N97  : N ninety-seven
  N98  : N ninety-eight
  N99  : N ninety-nine
  N100 : N one-hundred
{-# ATP prove N91 #-}
{-# ATP prove N92 #-}
{-# ATP prove N93 #-}
{-# ATP prove N94 #-}
{-# ATP prove N95 #-}
{-# ATP prove N96 #-}
{-# ATP prove N97 #-}
{-# ATP prove N98 #-}
{-# ATP prove N99 #-}
{-# ATP prove N100 #-}

postulate
  N101 : N hundred-one
  N111 : N hundred-eleven
{-# ATP prove N101 #-}
{-# ATP prove N111 #-}
