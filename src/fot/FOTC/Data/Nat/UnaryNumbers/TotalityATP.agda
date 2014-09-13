------------------------------------------------------------------------------
-- The unary numbers are FOTC total natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Nat.UnaryNumbers.TotalityATP where

open import FOTC.Base
open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

postulate
  0-N : N 0'
  1-N : N 1'
  2-N : N 2'
  3-N : N 3'
  4-N : N 4'
  5-N : N 5'
{-# ATP prove 0-N #-}
{-# ATP prove 1-N #-}
{-# ATP prove 2-N #-}
{-# ATP prove 3-N #-}
{-# ATP prove 4-N #-}
{-# ATP prove 5-N #-}

postulate
  10-N : N 10'
  11-N : N 11'
{-# ATP prove 10-N #-}
{-# ATP prove 11-N #-}

postulate 89-N : N 89'
{-# ATP prove 89-N #-}

postulate
  90-N : N 90'
  91-N : N 91'
  92-N : N 92'
  93-N : N 93'
  94-N : N 94'
  95-N : N 95'
  96-N : N 96'
  97-N : N 97'
  98-N : N 98'
  99-N : N 99'
{-# ATP prove 90-N #-}
{-# ATP prove 91-N #-}
{-# ATP prove 92-N #-}
{-# ATP prove 93-N #-}
{-# ATP prove 94-N #-}
{-# ATP prove 95-N #-}
{-# ATP prove 96-N #-}
{-# ATP prove 97-N #-}
{-# ATP prove 98-N #-}
{-# ATP prove 99-N #-}

postulate
  100-N : N 100'
  101-N : N 101'
{-# ATP prove 100-N #-}
{-# ATP prove 101-N #-}

postulate 111-N : N 111'
{-# ATP prove 111-N #-}
