------------------------------------------------------------------------------
-- The unary numbers are FOTC natural numbers
------------------------------------------------------------------------------

module FOTC.Data.Nat.UnaryNumbers.IsN-ATP where

open import FOTC.Base

open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

postulate
  0-N  : N zero
  1-N  : N one
  2-N  : N two
  10-N : N ten
{-# ATP prove 0-N #-}
{-# ATP prove 1-N #-}
{-# ATP prove 2-N #-}
{-# ATP prove 10-N #-}

postulate
  11-N : N eleven
{-# ATP prove 11-N #-}

postulate
  89-N : N eighty-nine
  90-N : N ninety
{-# ATP prove 89-N #-}
{-# ATP prove 90-N #-}

postulate
  91-N  : N ninety-one
  92-N  : N ninety-two
  93-N  : N ninety-three
  94-N  : N ninety-four
  95-N  : N ninety-five
  96-N  : N ninety-six
  97-N  : N ninety-seven
  98-N  : N ninety-eight
  99-N  : N ninety-nine
  100-N : N one-hundred
{-# ATP prove 91-N #-}
{-# ATP prove 92-N #-}
{-# ATP prove 93-N #-}
{-# ATP prove 94-N #-}
{-# ATP prove 95-N #-}
{-# ATP prove 96-N #-}
{-# ATP prove 97-N #-}
{-# ATP prove 98-N #-}
{-# ATP prove 99-N #-}
{-# ATP prove 100-N #-}

postulate
  101-N : N hundred-one
  111-N : N hundred-eleven
{-# ATP prove 101-N #-}
{-# ATP prove 111-N #-}
