------------------------------------------------------------------------------
-- Well-founded relation on lists based on their structure
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.List.WF-Relation.LT-Cons where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List

------------------------------------------------------------------------------
-- Well-founded relation on lists based on their structure.
LTC : D → D → Set
LTC xs ys = ∃[ x ] ys ≡ x ∷ xs
