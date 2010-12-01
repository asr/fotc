------------------------------------------------------------------------------
-- Test the consistency of LTC.Program.SortList.SortList
------------------------------------------------------------------------------

module Test.Consistency.LTC.Program.SortList.SortList.Impossible where

open import LTC.Base

open import LTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- See Test.Consistency.README
postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
