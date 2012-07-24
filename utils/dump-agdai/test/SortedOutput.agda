------------------------------------------------------------------------------
-- Testing the sorted output of the @QName@s.
------------------------------------------------------------------------------

module SortedOutput where

postulate A : Set

postulate b : A

data Bool : Set where
  true  : Bool
  false : Bool

foo : Bool → Bool
foo b = b

postulate a : A
