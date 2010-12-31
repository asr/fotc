------------------------------------------------------------------------------
-- Sort a list
------------------------------------------------------------------------------

-- This module define the program which sorts a list by converting it
-- into an ordered tree and then back to a list (Burstall, 1969, pp. 45-46).

-- R. M. Burstall. Proving properties of programs by structural
-- induction. The Computer Journal, 12(1):41–48, 1969.

module LTC.Program.SortList.SortList where

open import LTC.Base

open import LTC.Data.Bool using ( _&&_ )
open import LTC.Data.Nat.Inequalities using ( _≤_ )
open import LTC.Data.Nat.Type
  using ( N  -- The LTC natural numbers type.
        )
open import LTC.Data.List using ( _++_ )

------------------------------------------------------------------------------
-- Tree terms
postulate
  nilTree  : D
  tip      : D → D
  node     : D → D → D → D

-- The LTC tree type.
data Tree : D → Set where
  nilT  : Tree nilTree
  tipT  : {i : D} → N i → Tree (tip i)
  nodeT : {t₁ i t₂ : D} → Tree t₁ → N i → Tree t₂ → Tree (node t₁ i t₂)
{-# ATP hint nilT #-}
{-# ATP hint tipT #-}
{-# ATP hint nodeT #-}

------------------------------------------------------------------------------
-- Inequalites on lists and trees

-- Note from Burstall (p. 46): "The relation ≤ between lists is only an
-- ordering if nil is excluded, similarly for trees. This is untidy but
-- will not cause trouble."

postulate
  ≤-ItemList    : D → D → D
  ≤-ItemList-[] : (item : D) → ≤-ItemList item [] ≡ true
  ≤-ItemList-∷  : (item i is : D) →
                    ≤-ItemList item (i ∷ is) ≡ item ≤ i && ≤-ItemList item is
{-# ATP axiom ≤-ItemList-[] #-}
{-# ATP axiom ≤-ItemList-∷ #-}

LE-ItemList : D → D → Set
LE-ItemList item is = ≤-ItemList item is ≡ true
{-# ATP definition LE-ItemList #-}

postulate
  ≤-Lists    : D → D → D
  ≤-Lists-[] : (is : D) → ≤-Lists [] is ≡ true
  ≤-Lists-∷  : (i is js : D) →
                  ≤-Lists (i ∷ is) js ≡ ≤-ItemList i js && ≤-Lists is js
{-# ATP axiom ≤-Lists-[] #-}
{-# ATP axiom ≤-Lists-∷ #-}

LE-Lists : D → D → Set
LE-Lists is js = ≤-Lists is js ≡ true
{-# ATP definition LE-Lists #-}

postulate
  ≤-ItemTree          : D → D → D
  ≤-ItemTree-nilTree  : (item : D) →   ≤-ItemTree item nilTree ≡ true
  ≤-ItemTree-tip      : (item i : D) → ≤-ItemTree item (tip i) ≡ item ≤ i
  ≤-ItemTree-node     : (item t₁ i t₂ : D) →
                          ≤-ItemTree item (node t₁ i t₂) ≡
                          ≤-ItemTree item t₁ && ≤-ItemTree item t₂
{-# ATP axiom ≤-ItemTree-nilTree #-}
{-# ATP axiom ≤-ItemTree-tip #-}
{-# ATP axiom ≤-ItemTree-node #-}

LE-ItemTree : D → D → Set
LE-ItemTree item t = ≤-ItemTree item t ≡ true
{-# ATP definition LE-ItemTree #-}

-- This function is not defined in the paper.
postulate
  ≤-TreeItem         : D → D → D
  ≤-TreeItem-nilTree : (item : D) →   ≤-TreeItem nilTree item ≡ true
  ≤-TreeItem-tip     : (i item : D) → ≤-TreeItem (tip i) item ≡ i ≤ item
  ≤-TreeItem-node    : (t₁ i t₂ item : D) →
                         ≤-TreeItem (node t₁ i t₂) item ≡
                         ≤-TreeItem t₁ item && ≤-TreeItem t₂ item
{-# ATP axiom ≤-TreeItem-nilTree #-}
{-# ATP axiom ≤-TreeItem-tip #-}
{-# ATP axiom ≤-TreeItem-node #-}

LE-TreeItem : D → D → Set
LE-TreeItem t item = ≤-TreeItem t item ≡ true
{-# ATP definition LE-TreeItem #-}

------------------------------------------------------------------------------
-- Auxiliary functions

postulate
  -- The foldr function with the last two args flipped.
  lit    : D → D → D → D
  lit-[] : (f n : D) →      lit f []       n ≡ n
  lit-∷  : (f d ds n : D) → lit f (d ∷ ds) n ≡ f · d · (lit f ds n)
{-# ATP axiom lit-[] #-}
{-# ATP axiom lit-∷ #-}

------------------------------------------------------------------------------
-- Ordering functions and predicates on lists and trees

postulate
  ordList    : D → D
  ordList-[] :              ordList []       ≡ true
  ordList-∷  : (i is : D) → ordList (i ∷ is) ≡ ≤-ItemList i is && ordList is
{-# ATP axiom ordList-[] #-}
{-# ATP axiom ordList-∷ #-}

OrdList : D → Set
OrdList is = ordList is ≡ true
{-# ATP definition OrdList #-}

postulate
  ordTree         : D → D
  ordTree-nilTree :            ordTree nilTree ≡ true
  ordTree-tip     : (i : D) →  ordTree (tip i) ≡ true
  ordTree-node    : (t₁ i t₂ : D) →
                      ordTree (node t₁ i t₂) ≡
                      ordTree t₁ && ordTree t₂ && ≤-TreeItem t₁ i && ≤-ItemTree i t₂
{-# ATP axiom ordTree-nilTree #-}
{-# ATP axiom ordTree-tip #-}
{-# ATP axiom ordTree-node #-}

OrdTree : D → Set
OrdTree t = ordTree t ≡ true
{-# ATP definition OrdTree #-}

------------------------------------------------------------------------------
-- The program

-- The function toTree adds an item to a tree.

-- The items have an ordering ≤ defined over them. The item held at a
-- node of the tree is chosen so that the left subtree has items not
-- greater than it and the right subtree has items not less than it.

postulate
  toTree          : D
  toTree-nilTree  : (item : D) →   toTree · item · nilTree ≡ tip item
  toTree-tip      : (item i : D) → toTree · item · (tip i) ≡
                    if (i ≤ item)
                      then (node (tip i) item (tip item))
                      else (node (tip item) i (tip i))
  toTree-node     : (item t₁ i t₂ : D) →
                    toTree · item · (node t₁ i t₂) ≡
                       if (i ≤ item)
                         then (node t₁ i (toTree · item · t₂))
                         else (node (toTree · item · t₁) i t₂)
{-# ATP axiom toTree-nilTree #-}
{-# ATP axiom toTree-tip #-}
{-# ATP axiom toTree-node #-}

-- The function makeTree converts a list to a tree.
makeTree : D → D
makeTree is = lit toTree is nilTree
{-# ATP definition makeTree #-}

-- The function flatten converts a tree to a list.
postulate
  flatten         : D → D
  flatten-nilTree :           flatten nilTree ≡ []
  flatten-tip     : (i : D) → flatten (tip i) ≡ i ∷ []
  flatten-node    : (t₁ i t₂ : D) →
                      flatten (node t₁ i t₂)  ≡ flatten t₁ ++ flatten t₂
{-# ATP axiom flatten-nilTree #-}
{-# ATP axiom flatten-tip #-}
{-# ATP axiom flatten-node #-}

-- The function which sorts the list
sort : D → D
sort is = flatten (makeTree is)
{-# ATP definition sort #-}
