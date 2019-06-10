------------------------------------------------------------------------------
-- Sort a list
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module define the program which sorts a list by converting it
-- into an ordered tree and then back to a list (Burstall 1969,
-- pp. 45-46).

module Interactive.FOTC.Program.SortList.SortList where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Data.Bool
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Tree terms.
postulate
  nil  : D
  tip  : D → D
  node : D → D → D → D

-- The tree type.
data Tree : D → Set where
  tnil  : Tree nil
  ttip  : ∀ {i} → N i → Tree (tip i)
  tnode : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ → Tree (node t₁ i t₂)

------------------------------------------------------------------------------
-- Inequalites on lists and trees

-- Note from Burstall (p. 46): "The relation ≤ between lists is only an
-- ordering if nil is excluded, similarly for trees. This is untidy but
-- will not cause trouble."

postulate
  le-ItemList    : D → D → D
  le-ItemList-[] : ∀ item → le-ItemList item [] ≡ true
  le-ItemList-∷  : ∀ item i is →
                   le-ItemList item (i ∷ is) ≡ le item i && le-ItemList item is

≤-ItemList : D → D → Set
≤-ItemList item is = le-ItemList item is ≡ true

postulate
  le-Lists    : D → D → D
  le-Lists-[] : ∀ is → le-Lists [] is ≡ true
  le-Lists-∷  : ∀ i is js →
                le-Lists (i ∷ is) js ≡ le-ItemList i js && le-Lists is js

≤-Lists : D → D → Set
≤-Lists is js = le-Lists is js ≡ true

postulate
  le-ItemTree      : D → D → D
  le-ItemTree-nil  : ∀ item → le-ItemTree item nil ≡ true
  le-ItemTree-tip  : ∀ item i → le-ItemTree item (tip i) ≡ le item i
  le-ItemTree-node : ∀ item t₁ i t₂ →
                     le-ItemTree item (node t₁ i t₂) ≡
                     le-ItemTree item t₁ && le-ItemTree item t₂

≤-ItemTree : D → D → Set
≤-ItemTree item t = le-ItemTree item t ≡ true

-- This function is not defined in the paper.
postulate
  le-TreeItem      : D → D → D
  le-TreeItem-nil  : ∀ item → le-TreeItem nil item ≡ true
  le-TreeItem-tip  : ∀ i item → le-TreeItem (tip i) item ≡ le i item
  le-TreeItem-node : ∀ t₁ i t₂ item →
                     le-TreeItem (node t₁ i t₂) item ≡
                     le-TreeItem t₁ item && le-TreeItem t₂ item

≤-TreeItem : D → D → Set
≤-TreeItem t item = le-TreeItem t item ≡ true

------------------------------------------------------------------------------
-- Auxiliary functions

postulate
  -- The foldr function with the last two args flipped.
  lit    : D → D → D → D
  lit-[] : ∀ f n → lit f [] n            ≡ n
  lit-∷  : ∀ f d ds n → lit f (d ∷ ds) n ≡ f · d · (lit f ds n)

------------------------------------------------------------------------------
-- Ordering functions and predicates on lists and trees

postulate
  ordList    : D → D
  ordList-[] : ordList []                ≡ true
  ordList-∷  : ∀ i is → ordList (i ∷ is) ≡ le-ItemList i is && ordList is

OrdList : D → Set
OrdList is = ordList is ≡ true

postulate
  ordTree      : D → D
  ordTree-nil  : ordTree nil ≡ true
  ordTree-tip  : ∀ i → ordTree (tip i) ≡ true
  ordTree-node : ∀ t₁ i t₂ →
                 ordTree (node t₁ i t₂) ≡
                 ordTree t₁ && ordTree t₂ && le-TreeItem t₁ i && le-ItemTree i t₂

OrdTree : D → Set
OrdTree t = ordTree t ≡ true

------------------------------------------------------------------------------
-- The program

-- The function toTree adds an item to a tree.

-- The items have an ordering ≤ defined over them. The item held at a
-- node of the tree is chosen so that the left subtree has items not
-- greater than it and the right subtree has items not less than it.

postulate
  toTree      : D
  toTree-nil  : ∀ item → toTree · item · nil ≡ tip item
  toTree-tip  : ∀ item i → toTree · item · (tip i) ≡
                (if (le i item)
                   then (node (tip i) item (tip item))
                   else (node (tip item) i (tip i)))
  toTree-node : ∀ item t₁ i t₂ →
                toTree · item · (node t₁ i t₂) ≡
                (if (le i item)
                   then (node t₁ i (toTree · item · t₂))
                   else (node (toTree · item · t₁) i t₂))

-- The function makeTree converts a list to a tree.
makeTree : D → D
makeTree is = lit toTree is nil

-- The function flatten converts a tree to a list.
postulate
  flatten      : D → D
  flatten-nil  : flatten nil ≡ []
  flatten-tip  : ∀ i → flatten (tip i) ≡ i ∷ []
  flatten-node : ∀ t₁ i t₂ → flatten (node t₁ i t₂) ≡ flatten t₁ ++ flatten t₂

-- The function which sorts the list
sort : D → D
sort is = flatten (makeTree is)

------------------------------------------------------------------------------
-- References
--
-- Burstall, R. M. (1969). Proving properties of programs by
-- structural induction. The Computer Journal 12.1, pp. 41–48.
