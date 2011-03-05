-- Tested with the development version of the standard library on
-- 05 March 2011.

module MirrorSL where

open import Algebra
open import Data.List as List hiding ( reverse )
open import Data.List.Properties

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module LM {A : Set} = Monoid (List.monoid A)

------------------------------------------------------------------------------

reverse : {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ x ∷ []

++-rightIdentity : {A : Set}(xs : List A) → xs ++ [] ≡ xs
++-rightIdentity []       = refl
++-rightIdentity (x ∷ xs) = cong (_∷_ x) (++-rightIdentity xs)

reverse-++ : {A : Set}(xs ys : List A) →
             reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++ [] ys       = sym (++-rightIdentity (reverse ys))
reverse-++ (x ∷ xs) [] = cong (λ x' → reverse x' ++ x ∷ []) (++-rightIdentity xs)
reverse-++ (x ∷ xs) (y ∷ ys) =
  begin
    reverse (xs ++ y ∷ ys) ++ x ∷ []
      ≡⟨ cong (λ x' → x' ++ x ∷ []) (reverse-++ xs (y ∷ ys)) ⟩
    (reverse (y ∷ ys) ++ reverse xs) ++ x ∷ []
      ≡⟨ LM.assoc (reverse (y ∷ ys)) (reverse xs) (x ∷ []) ⟩
    reverse (y ∷ ys) ++ reverse (x ∷ xs)
  ∎

data Tree (A : Set) : Set where
  treeT : A → List (Tree A) → Tree A

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
           (aux (t ∷ ts))
           refl
        ⟩
      treeT a (t ∷ ts)
    ∎

  aux : {A : Set} → (ts : List (Tree A)) →
        reverse (map mirror (reverse (map mirror ts))) ≡ ts
  aux []       = refl
  aux (t ∷ ts) =
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
                 (reverse-++ (map mirror (reverse (map mirror ts)))
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
                 (aux ts)
                 refl
        ⟩
      t ∷ ts
    ∎
