------------------------------------------------------------------------------
-- The relation LTL is well-founded using the image inverse combinator
-- from the standard library
------------------------------------------------------------------------------

module LT-LengthSL {A : Set} where

open import Data.List
open import Data.Nat

open import Induction.Nat
open import Induction.WellFounded

open module II =
  Induction.WellFounded.Inverse-image length

LTL : List A → List A → Set
LTL xs ys = (length xs) <′ (length ys)

wfLTL : Well-founded LTL
wfLTL = well-founded <-well-founded
