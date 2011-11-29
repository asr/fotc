-- Tested with the development versions of Agda and the standard library on
-- 29 November 2011.

module MirrorRoseTreeSL where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

infixr 5 _∷_ _++_

------------------------------------------------------------------------------

mutual
  data Tree (A : Set) : Set where
    treeT : A → Forest A → Tree A

  data Forest (A : Set) : Set where
    []  : Forest A
    _∷_ : Tree A → Forest A → Forest A

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

mirror : {A : Set} → Tree A → Tree A
mirror (treeT a ts) = treeT a (reverse (map mirror ts))

mutual
  mirror² : {A : Set} → (t : Tree A) → mirror (mirror t) ≡ t
  mirror² (treeT a [])       = refl
  mirror² (treeT a (t ∷ ts)) =
    begin
      treeT a (reverse (map mirror (reverse (map mirror ts) ++ mirror t ∷ [])))
        ≡⟨ subst (λ x → treeT a (reverse (map mirror (reverse (map mirror ts) ++
                                                      mirror t ∷ []))) ≡
                        treeT a x)
           (helper (t ∷ ts))
           refl
        ⟩
      treeT a (t ∷ ts)
    ∎

  helper : {A : Set} → (ts : Forest A) →
           reverse (map mirror (reverse (map mirror ts))) ≡ ts
  helper []       = refl
  helper (t ∷ ts) =
    begin
      reverse (map mirror (reverse (map mirror ts) ++ mirror t ∷ []))
        ≡⟨ subst (λ x → (reverse (map mirror (reverse (map mirror ts) ++
                                              mirror t ∷ []))) ≡
                        reverse x)
           (map-++-commute mirror (reverse (map mirror ts)) (mirror t ∷ []))
           refl
        ⟩
      reverse (map mirror (reverse (map mirror ts)) ++
              (map mirror (mirror t ∷ [])))
        ≡⟨ subst (λ x → (reverse (map mirror (reverse (map mirror ts)) ++
                                             (map mirror (mirror t ∷ [])))) ≡
                        x)
                 (reverse-++-commute (map mirror (reverse (map mirror ts)))
                                     (map mirror (mirror t ∷ [])))
                 refl
        ⟩
      reverse (map mirror (mirror t ∷ [])) ++
      reverse (map mirror (reverse (map mirror ts)))
              ≡⟨ refl ⟩
      mirror (mirror t) ∷ reverse (map mirror (reverse (map mirror ts)))
        ≡⟨ subst (λ x → (mirror (mirror t) ∷
                                reverse (map mirror (reverse (map mirror ts)))) ≡
                        (x ∷ reverse (map mirror (reverse (map mirror ts)))))
                 (mirror² t)  -- IH.
                 refl
        ⟩
      t ∷ reverse (map mirror (reverse (map mirror ts)))
        ≡⟨ subst (λ x → t ∷ reverse (map mirror (reverse (map mirror ts))) ≡
                        t ∷ x)
                 (helper ts)
                 refl
        ⟩
      t ∷ ts
    ∎
