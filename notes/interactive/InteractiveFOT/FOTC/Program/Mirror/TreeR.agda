------------------------------------------------------------------------------
-- Well-founded relation on trees
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Program.Mirror.TreeR where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.List.WF-Relation.LT-Cons
open import Interactive.FOTC.Program.Mirror.Type

------------------------------------------------------------------------------
-- Well-founded relation on trees.

-- A well-founded relation for rose trees is the lexicographical order
--
-- (t : ts) < (t' : ts') = t < t' or t ≡ t' and ts < ts'.
--
-- It seems we would not to use the first conjunct in the mirror
-- example.
TreeR : D → D → Set
TreeR t₁ t₂ = ∃[ d ] ∃[ ts₁ ] ∃[ ts₂ ]
                 t₁ ≡ node d ts₁
                 ∧ t₂ ≡ node d ts₂
                 ∧ LTC ts₁ ts₂
