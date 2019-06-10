------------------------------------------------------------------------------
-- Well-founded relation on lists based on their length
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.List.WF-Relation.LT-Length where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.List
open import Combined.FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------
-- Well-founded relation on lists based on their length.
LTL : D → D → Set
LTL xs ys = length xs < length ys
