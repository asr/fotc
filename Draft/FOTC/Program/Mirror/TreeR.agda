------------------------------------------------------------------------------
-- Well-founded relation on trees
------------------------------------------------------------------------------

module Draft.FOTC.Program.Mirror.TreeR where

open import FOTC.Base

open import FOTC.Data.List.LT-Cons

open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------
-- Well-founded relation on trees.
-- A well-founded relation for rose trees is the lexicographical order
-- (t : ts) < (t' : ts') = t < t' or t ≡ t' and ts < ts'
-- It seeems we would not to use the first disjunct in the mirror example.
TreeR : D → D → Set
TreeR t₁ t₂ = ∃D (λ d →
              ∃D (λ ts₁ →
              ∃D (λ ts₂ → t₁ ≡ node d ts₁ ∧
                          t₂ ≡ node d ts₂ ∧
                          LTC ts₁ ts₂)))
