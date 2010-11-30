------------------------------------------------------------------------------
-- Test the consistency of Examples.SortList.SortList
------------------------------------------------------------------------------

module Test.Consistency.Examples.SortList.SortList.Impossible where

open import LTC.Base

open import Examples.SortList.SortList

------------------------------------------------------------------------------
-- See Test.Consistency.README.txt
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
