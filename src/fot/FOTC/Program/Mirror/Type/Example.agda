------------------------------------------------------------------------------
-- Tree example
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Mirror.Type.Example where

open import FOTC.Base
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------
-- Example
--       1
--    / / \ \
--   2 3   4 5
--  / \
-- 6   7

t : D
t = node 1' (node 2' (node 6' [] ∷ node 7' [] ∷ []) ∷
             node 3' [] ∷
             node 4' [] ∷
             node 5' [] ∷
             []
            )

tTree : Tree t
tTree = tree 1' (fcons (tree 2' (fcons (tree 6' fnil)
                                (fcons (tree 7' fnil)
                                fnil)))
                (fcons (tree 3' fnil)
                (fcons (tree 4' fnil)
                (fcons (tree 5' fnil)
                fnil))))
