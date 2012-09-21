------------------------------------------------------------------------------
-- Well-founded relation on lists based on their structure
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.List.LT-Cons where

open import FOTC.Base
open FOTC.Base.BList

------------------------------------------------------------------------------
-- Well-founded relation on lists based on their structure.
LTC : D → D → Set
LTC xs ys = ∃[ x ] ys ≡ x ∷ xs
