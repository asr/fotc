
module Mirror where

------------------------------------------------------------------------------
-- Using mutually recursive data types
data Tree a = Tree a (Forest a)
              deriving Eq

data Forest a = Fnil | Fcons (Tree a) (Forest a)
              deriving Eq

--       1
--    / / \ \
--   2 3   4 5
--  / \
-- 6   7

tTree :: Tree Int
tTree = Tree 1 (Fcons (Tree 2
                         (Fcons (Tree 6 Fnil)
                         (Fcons (Tree 7 Fnil)
                         Fnil)))
               (Fcons (Tree 3 Fnil)
               (Fcons (Tree 4 Fnil)
               (Fcons (Tree 5 Fnil)
               Fnil))))

mapForest :: (Tree a -> Tree b) -> Forest a -> Forest b
mapForest _ Fnil         = Fnil
mapForest f (Fcons t ts) = Fcons (f t) (mapForest f ts)

reverseForest :: Forest a -> Forest a
reverseForest ts = revForest ts Fnil
  where
  revForest :: Forest a -> Forest a -> Forest a
  revForest Fnil         ys = ys
  revForest (Fcons x xs) ys = revForest xs (Fcons x ys)

mirrorTree :: Tree a -> Tree a
mirrorTree (Tree t ts) = Tree t (reverseForest (mapForest mirrorTree ts))

testTree :: Bool
testTree = tTree == mirrorTree (mirrorTree tTree)

------------------------------------------------------------------------------
-- Using a single data type
data Rose a = Rose a [Rose a]
              deriving Eq

--       1
--    / / \ \
--   2 3   4 5
--  / \
-- 6   7

tRose :: Rose Int
tRose = Rose 1 [ Rose 2 [ Rose 6 []
                        , Rose 7 []
                        ]
               , Rose 3 []
               , Rose 4 []
               , Rose 5 []
               ]

mirrorRose :: Rose a -> Rose a
mirrorRose (Rose a ts) = Rose a (reverse (map mirrorRose ts))

testRose :: Bool
testRose = tRose == mirrorRose (mirrorRose tRose)
