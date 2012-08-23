-- From Ralph Matthes' thesis.

module Matthes where

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data tree (A : Set) : Set where
  []     : tree A
  branch : A → tree A

data tree' (A : Set) : Set where
  []     : tree' A
  succ   : tree' A
  branch : A → tree' A

tree₁ : Set
tree₁ = tree Nat

data fin (A : Set) : Set where
  c : List A → fin A

-- Error: cont is not strictly positive, because it occurs to the left of
-- an arrow in the type of the constructor c in the definition of cont.
--
-- data cont (A : Set) : Set where
--   [] : cont A
--   c  : ((cont A → A) → A) → cont A

-- Error: Tree is not strictly positive, because it occurs in the
-- first argument to tree to the left of an arrow in the type of the
-- constructor branch in the definition of Tree.
--
-- data Tree : Set where
--   []     : Tree
--   branch : (tree(Tree) → Tree) → Tree
