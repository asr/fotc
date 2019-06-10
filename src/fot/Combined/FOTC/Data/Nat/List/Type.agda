----------------------------------------------------------------------------
-- The FOTC lists of natural numbers type
----------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.Nat.List.Type where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- The FOTC lists of natural numbers type (inductive predicate for
-- total lists of natural numbers).
data ListN : D → Set where
  lnnil  : ListN []
  lncons : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)
{-# ATP axioms lnnil lncons #-}

-- Induction principle.
ListN-ind : (A : D → Set) →
            A [] →
            (∀ {n ns} → N n → A ns → A (n ∷ ns)) →
            ∀ {ns} → ListN ns → A ns
ListN-ind A A[] h lnnil           = A[]
ListN-ind A A[] h (lncons Nn Lns) = h Nn (ListN-ind A A[] h Lns)
