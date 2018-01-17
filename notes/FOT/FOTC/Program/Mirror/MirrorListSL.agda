------------------------------------------------------------------------------
-- Proving mirror (mirror t) = t using a list of trees
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Program.Mirror.MirrorListSL where

open import Algebra
open import Function
open import Data.List hiding ( reverse )
open import Data.List.Properties
open import Data.Product hiding ( map )

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module LM {A : Set} = Monoid (++-monoid A)

------------------------------------------------------------------------------
-- Auxiliary functions

reverse : {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ x ∷ []

++-rightIdentity : {A : Set}(xs : List A) → xs ++ [] ≡ xs
++-rightIdentity = proj₂ LM.identity

reverse-++ : {A : Set}(xs ys : List A) →
             reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ [] ys       = sym (++-rightIdentity (reverse ys))
reverse-++ (x ∷ xs) [] = cong (λ x' → reverse x' ++ x ∷ [])
                              (++-rightIdentity xs)
reverse-++ (x ∷ xs) (y ∷ ys) =
  begin
    reverse (xs ++ y ∷ ys) ++ x ∷ []
      ≡⟨ cong (λ x' → x' ++ x ∷ []) (reverse-++ xs (y ∷ ys)) ⟩
    (reverse (y ∷ ys) ++ reverse xs) ++ x ∷ []
      ≡⟨ LM.assoc (reverse (y ∷ ys)) (reverse xs) (x ∷ []) ⟩
    reverse (y ∷ ys) ++ reverse (x ∷ xs)
  ∎

------------------------------------------------------------------------------
-- The rose tree type.
data Tree (A : Set) : Set where
  tree : A → List (Tree A) → Tree A

------------------------------------------------------------------------------
-- The mirror function.

{-# TERMINATING #-}
mirror : {A : Set} → Tree A → Tree A
mirror (tree a ts) = tree a (reverse (map mirror ts))

-- The proof of the property.
mirror-involutive : {A : Set} → (t : Tree A) → mirror (mirror t) ≡ t
helper            : {A : Set} → (ts : List (Tree A)) →
                    reverse (map mirror (reverse (map mirror ts))) ≡ ts

mirror-involutive (tree a []) = refl
mirror-involutive (tree a (t ∷ ts)) =
  begin
    tree a (reverse (map mirror (reverse (map mirror ts) ++ mirror t ∷ [])))
      ≡⟨ cong (tree a) (helper (t ∷ ts)) ⟩
    tree a (t ∷ ts)
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
               (reverse-++ (map mirror (reverse (map mirror ts)))
                           (map mirror (mirror t ∷ [])))
               refl
      ⟩
    reverse (map mirror (mirror t ∷ [])) ++
    reverse (map mirror (reverse (map mirror ts)))
      ≡⟨ refl ⟩
    mirror (mirror t) ∷ reverse (map mirror (reverse (map mirror ts)))
      ≡⟨ cong (flip _∷_ (reverse (map mirror (reverse (map mirror ts)))))
              (mirror-involutive t)
      ⟩
    t ∷ reverse (map mirror (reverse (map mirror ts)))
      ≡⟨ cong (_∷_ t) (helper ts) ⟩
    t ∷ ts
  ∎
