----------------------------------------------------------------------------
-- The FOTC lists of natural numbers type
----------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.List.Type where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- The FOTC lists of natural numbers type (inductive predicate for
-- total lists of natural numbers).
data ListN : D → Set where
  lnnil  : ListN []
  lncons : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)
{-# ATP axiom lnnil lncons #-}

-- Induction principle.
ListN-ind : (A : D → Set) →
            A [] →
            (∀ {n ns} → N n → A ns → A (n ∷ ns)) →
            ∀ {ns} → ListN ns → A ns
ListN-ind A A[] h lnnil           = A[]
ListN-ind A A[] h (lncons Nn Lns) = h Nn (ListN-ind A A[] h Lns)
