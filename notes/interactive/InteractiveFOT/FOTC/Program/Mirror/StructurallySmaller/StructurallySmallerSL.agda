
{-# OPTIONS --exact-split    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --without-K      #-}

module InteractiveFOT.FOTC.Program.Mirror.StructurallySmaller.StructurallySmallerSL where

open import Data.List

data Tree (D : Set) : Set where
  tree : D → List (Tree D) → Tree D

foo : {D : Set} → Tree D → D
foo (tree a [])       = a
foo (tree a (t ∷ ts)) = foo (tree a ts)

bar : {D : Set} → Tree D → D
bar     (tree a [])       = a
bar {D} (tree a (t ∷ ts)) = helper (bar t) (bar (tree a ts))
  where
  postulate helper : D → D → D
