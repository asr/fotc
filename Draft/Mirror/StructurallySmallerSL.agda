module StructurallySmallerSL where

open import Data.List

data Tree (A : Set) : Set where
  treeT : A → List (Tree A) → Tree A

foo : {A : Set} → Tree A → A
foo (treeT a [])       = a
foo (treeT a (x ∷ xs)) = foo (treeT a xs)
