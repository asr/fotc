{-# LANGUAGE UnicodeSyntax #-}

------------------------------------------------------------------------------
-- Using mutual data types
data Tree a   = Tree a (Forest a)
data Forest a = Fnil | Fcons (Tree a) (Forest a)

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

mirrorRoseTree ∷ RoseTree a → RoseTree a
mirrorRoseTree (RoseTree a ts) = RoseTree a (reverse (map mirrorRoseTree ts))
