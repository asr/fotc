------------------------------------------------------------------------------
-- Proving mirror (mirror t) = t using a list of trees
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of the standard library on
-- 31 May 2012.

module MirrorListSL where

open import Algebra
open import Function
open import Data.List as List hiding ( reverse )
open import Data.List.Properties hiding ( reverse-++-commute )
open import Data.Product hiding ( map )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module LM {A : Set} = Monoid (List.monoid A)

------------------------------------------------------------------------------
-- Auxiliary functions

reverse : {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ x ∷ []

++-rightIdentity : {A : Set}(xs : List A) → xs ++ [] ≡ xs
++-rightIdentity = proj₂ LM.identity

reverse-++-commute : {A : Set}(xs ys : List A) →
                     reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute [] ys       = sym (++-rightIdentity (reverse ys))
reverse-++-commute (x ∷ xs) [] = cong (λ x' → reverse x' ++ x ∷ [])
                                      (++-rightIdentity xs)
reverse-++-commute (x ∷ xs) (y ∷ ys) =
  begin
    reverse (xs ++ y ∷ ys) ++ x ∷ []
      ≡⟨ cong (λ x' → x' ++ x ∷ []) (reverse-++-commute xs (y ∷ ys)) ⟩
    (reverse (y ∷ ys) ++ reverse xs) ++ x ∷ []
      ≡⟨ LM.assoc (reverse (y ∷ ys)) (reverse xs) (x ∷ []) ⟩
    reverse (y ∷ ys) ++ reverse (x ∷ xs)
  ∎

------------------------------------------------------------------------------
-- The rose tree type.
data Tree (A : Set) : Set where
  treeT : A → List (Tree A) → Tree A

------------------------------------------------------------------------------
-- The mirror function.
mirror : {A : Set} → Tree A → Tree A
mirror (treeT a ts) = treeT a (reverse (map mirror ts))

-- The proof of the property.
mirror² : {A : Set} → (t : Tree A) → mirror (mirror t) ≡ t
helper  : {A : Set} → (ts : List (Tree A)) →
          reverse (map mirror (reverse (map mirror ts))) ≡ ts

mirror² (treeT a []) = refl
mirror² (treeT a (t ∷ ts)) =
  begin
    treeT a (reverse (map mirror (reverse (map mirror ts) ++ mirror t ∷ [])))
      ≡⟨ cong (treeT a) (helper (t ∷ ts)) ⟩
    treeT a (t ∷ ts)
  ∎

helper [] = refl
helper (t ∷ ts) =
  begin
    reverse (map mirror (reverse (map mirror ts) ++ mirror t ∷ []))
     ≡⟨ cong reverse
             (map-++-commute mirror (reverse (map mirror ts)) (mirror t ∷ []))
     ⟩
    reverse (map mirror (reverse (map mirror ts)) ++
            (map mirror (mirror t ∷ [])))
      ≡⟨ subst (λ x → (reverse (map mirror (reverse (map mirror ts)) ++
                                    (map mirror (mirror t ∷ [])))) ≡ x)
               (reverse-++-commute (map mirror (reverse (map mirror ts)))
                                   (map mirror (mirror t ∷ [])))
               refl
      ⟩
    reverse (map mirror (mirror t ∷ [])) ++
    reverse (map mirror (reverse (map mirror ts)))
      ≡⟨ refl ⟩
    mirror (mirror t) ∷ reverse (map mirror (reverse (map mirror ts)))
      ≡⟨ cong (flip _∷_ (reverse (map mirror (reverse (map mirror ts)))))
              (mirror² t)
      ⟩
    t ∷ reverse (map mirror (reverse (map mirror ts)))
      ≡⟨ cong (_∷_ t) (helper ts) ⟩
    t ∷ ts
  ∎
