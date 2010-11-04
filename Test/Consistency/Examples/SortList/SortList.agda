------------------------------------------------------------------------------
-- Test the consistency of Examples.SortList.SortList
------------------------------------------------------------------------------

module Test.Consistency.Examples.SortList.SortList where

open import LTC.Base

open import Examples.SortList.SortList

------------------------------------------------------------------------------
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
