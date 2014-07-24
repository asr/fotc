{-# LANGUAGE UnicodeSyntax #-}

------------------------------------------------------------------------------
-- Using mutually recursive data types
data Tree a   = Tree a (Forest a)
data Forest a = Fnil | Fcons (Tree a) (Forest a)

--       1
--    / / \ \
--   2 3   4 5
--  / \
-- 6   7

tTree ∷ Tree Int
tTree = Tree 1 (Fcons (Tree 2
                         (Fcons (Tree 6 Fnil)
                         (Fcons (Tree 7 Fnil)
                         Fnil)))
               (Fcons (Tree 3 Fnil)
               (Fcons (Tree 4 Fnil)
               (Fcons (Tree 5 Fnil)
               Fnil))))

mapForest ∷ (Tree a → Tree b) → Forest a → Forest b
mapForest _ Fnil         = Fnil
mapForest f (Fcons t ts) = Fcons (f t) (mapForest f ts)

reverseForest ∷ Forest a → Forest a
reverseForest ts = revForest ts Fnil
  where
  revForest ∷ Forest a → Forest a → Forest a
  revForest Fnil         ys = ys
  revForest (Fcons x xs) ys = revForest xs (Fcons x ys)

mirrorTree ∷ Tree a → Tree a
mirrorTree (Tree t ts) = Tree t (reverseForest (mapForest mirrorTree ts))

-- Using a single data type
data RoseTree a = RoseTree a [RoseTree a]

--       1
--    / / \ \
--   2 3   4 5
--  / \
-- 6   7

tRoseTree ∷ RoseTree Int
tRoseTree = RoseTree 1 [ RoseTree 2 [ RoseTree 6 []
                                    , RoseTree 7 []
                                    ]
                       , RoseTree 3 []
                       , RoseTree 4 []
                       , RoseTree 5 []
                       ]

mirrorRoseTree ∷ RoseTree a → RoseTree a
mirrorRoseTree (RoseTree a ts) = RoseTree a (reverse (map mirrorRoseTree ts))
