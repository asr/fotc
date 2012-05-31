------------------------------------------------------------------------------
-- Proving mirror (mirror t) = t using mutual data types
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of the standard library on
-- 31 May 2012.

module MirrorMutualSL where

infixr 5 _∷_ _++_

open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

------------------------------------------------------------------------------
-- The mutual data types

data Tree   (A : Set) : Set
data Forest (A : Set) : Set

data Tree A where
  treeT : A → Forest A → Tree A

data Forest A where
  []  : Forest A
  _∷_ : Tree A → Forest A → Forest A

------------------------------------------------------------------------------
-- Auxiliary functions

_++_ : {A : Set} → Forest A → Forest A → Forest A
[]       ++ ys = ys
(a ∷ xs) ++ ys = a ∷ xs ++ ys

map : {A B : Set} → (Tree A → Tree B) → Forest A → Forest B
map f []       = []
map f (a ∷ ts) = f a ∷ map f ts

reverse : {A : Set} → Forest A → Forest A
reverse []       = []
reverse (a ∷ ts) = reverse ts ++ a ∷ []

postulate
  map-++-commute     : {A B : Set}(f : Tree A → Tree B)(xs ys : Forest A) →
                       map f (xs ++ ys) ≡ map f xs ++ map f ys
  reverse-++-commute : {A : Set}(xs ys : Forest A) →
                       reverse (xs ++ ys) ≡ reverse ys ++ reverse xs

------------------------------------------------------------------------------
-- The mirror function.
mirror : {A : Set} → Tree A → Tree A
mirror (treeT a ts) = treeT a (reverse (map mirror ts))

------------------------------------------------------------------------------
-- The proof of the property.
mirror² : {A : Set} → (t : Tree A) → mirror (mirror t) ≡ t
helper : {A : Set} → (ts : Forest A) →
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
              (mirror² t)  -- IH
      ⟩
    t ∷ reverse (map mirror (reverse (map mirror ts)))
      ≡⟨ cong (_∷_ t) (helper ts) ⟩
    t ∷ ts
  ∎
