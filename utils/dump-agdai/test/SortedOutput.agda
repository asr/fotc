module SortedOutput where

postulate A : Set

postulate b : A

data Bool : Set where
  false true : Bool

foo : Bool → Bool
foo b = b

postulate a : A
