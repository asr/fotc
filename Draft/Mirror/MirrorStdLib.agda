module MirrorStdLib where

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

mirror² : {A : Set} → (t : Tree A) → mirror (mirror t) ≡ t
mirror² (treeT a [])       = refl
mirror² (treeT a (t ∷ ts)) =
  begin
    treeT a (reverse (map mirror (reverse (map mirror ts) ++ mirror t ∷ [])))
      ≡⟨ subst (λ x → treeT a (reverse (map mirror (reverse (map mirror ts) ++
                                                    mirror t ∷ []))) ≡
                      treeT a (reverse x))
         (map-++-commute mirror (reverse (map mirror ts)) (mirror t ∷ []))
         refl
      ⟩
    treeT a (reverse (map mirror (reverse (map mirror ts)) ++
                     (map mirror (mirror t ∷ []))))
      ≡⟨ subst (λ x → treeT a (reverse (map mirror (reverse (map mirror ts)) ++
                                       (map mirror (mirror t ∷ [])))) ≡
                      treeT a x)
               (reverse-++ (map mirror (reverse (map mirror ts)))
                           (map mirror (mirror t ∷ [])))
               refl
      ⟩
    treeT a (reverse (map mirror (mirror t ∷ [])) ++
             reverse (map mirror (reverse (map mirror ts))))
      ≡⟨ refl ⟩
    treeT a (mirror (mirror t) ∷ reverse (map mirror (reverse (map mirror ts))))
      ≡⟨ subst (λ x → treeT a (mirror (mirror t) ∷
                                reverse (map mirror (reverse (map mirror ts)))) ≡
                      treeT a (x ∷ reverse (map mirror (reverse (map mirror ts)))))
               (mirror² t)  -- IH.
               refl
      ⟩
    treeT a (t ∷ reverse (map mirror (reverse (map mirror ts))))
      ≡⟨ {!!} ⟩
    treeT a (t ∷ ts)
  ∎
