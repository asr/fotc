{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.Mirror.StructurallySmaller.StructurallySmallerSL where

open import Data.List

data Tree (D : Set) : Set where
  treeT : D → List (Tree D) → Tree D

foo : {D : Set} → Tree D → D
foo (treeT a [])       = a
foo (treeT a (t ∷ ts)) = foo (treeT a ts)

bar : {D : Set} → Tree D → D
bar     (treeT a [])       = a
bar {D} (treeT a (t ∷ ts)) = helper (bar t) (bar (treeT a ts))
  where
  postulate helper : D → D → D
