------------------------------------------------------------------------------
-- Well-founded relation on lists based on their length
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.List.WF-Relation.LT-Length where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- Well-founded relation on lists based on their length.
LTL : D → D → Set
LTL xs ys = length xs < length ys
