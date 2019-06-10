------------------------------------------------------------------------------
-- Mirror example
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.Mirror.Example where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.UnaryNumbers
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Program.Mirror.Mirror
open import Interactive.FOTC.Program.Mirror.Type
open import Interactive.FOTC.Program.Mirror.Properties

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

test : t ≡ mirror · (mirror · t)
test = sym (mirror-involutive tTree)
