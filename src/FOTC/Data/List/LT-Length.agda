------------------------------------------------------------------------------
-- Well-founded relation on lists based on their length
------------------------------------------------------------------------------

module FOTC.Data.List.LT-Length where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- Well-founded relation on lists based on their length.
LTL : D → D → Set
LTL xs ys = LT (length xs) (length ys)
