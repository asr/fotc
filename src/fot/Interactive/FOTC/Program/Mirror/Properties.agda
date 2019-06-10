------------------------------------------------------------------------------
-- Properties of the mirror function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.Mirror.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Base.List.Properties
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Data.List.Properties
open import Interactive.FOTC.Program.Mirror.Type
open import Interactive.FOTC.Program.Mirror.Forest.Properties as ForestP
open import Interactive.FOTC.Program.Mirror.Forest.Totality
open import Interactive.FOTC.Program.Mirror.Mirror
open import Interactive.FOTC.Program.Mirror.Tree.Totality

------------------------------------------------------------------------------

mirror-involutive : ∀ {t} → Tree t → mirror · (mirror · t) ≡ t
helper            : ∀ {ts} → Forest ts →
                    reverse (map mirror (reverse (map mirror ts))) ≡ ts

mirror-involutive (tree d fnil) =
  mirror · (mirror · (node d []))
    ≡⟨ subst (λ x → mirror · (mirror · (node d [])) ≡ mirror · x)
             (mirror-eq d [])
             refl
    ⟩
  mirror · node d (reverse (map mirror []))
    ≡⟨ subst (λ x → mirror · node d (reverse (map mirror [])) ≡
                    mirror · node d (reverse x))
             (map-[] mirror)
             refl
    ⟩
  mirror · node d (reverse [])
    ≡⟨ subst (λ x → mirror · node d (reverse []) ≡ mirror · node d x)
             (rev-[] [])
             refl
    ⟩
  mirror · node d []
    ≡⟨ mirror-eq d [] ⟩
  node d (reverse (map mirror []))
    ≡⟨ subst (λ x → node d (reverse (map mirror [])) ≡
                    node d (reverse x))
             (map-[] mirror)
             refl
    ⟩
  node d (reverse [])
    ≡⟨ subst (λ x → node d (reverse []) ≡ node d x) (rev-[] []) refl ⟩
  node d [] ∎

mirror-involutive (tree d (fcons {t} {ts} Tt Fts)) =
  mirror · (mirror · node d (t ∷ ts))
    ≡⟨ subst (λ x → mirror · (mirror · node d (t ∷ ts)) ≡ mirror · x)
             (mirror-eq d (t ∷ ts))
             refl
    ⟩
  mirror · node d (reverse (map mirror (t ∷ ts)))
    ≡⟨ subst (λ x → mirror · node d (reverse (map mirror (t ∷ ts))) ≡ x)
             (mirror-eq d (reverse (map mirror (t ∷ ts))))
             refl
    ⟩
  node d (reverse (map mirror (reverse (map mirror (t ∷ ts)))))
    ≡⟨ subst (λ x → node d (reverse (map mirror (reverse (map mirror (t ∷ ts))))) ≡
                    node d x)
             (helper (fcons Tt Fts))
             refl
    ⟩
  node d (t ∷ ts) ∎

helper fnil =
  reverse (map mirror (reverse (map mirror [])))
    ≡⟨ reverseCong (mapCong₂ (reverseCong (map-[] mirror))) ⟩
  reverse (map mirror (reverse []))
    ≡⟨ reverseCong (mapCong₂ (rev-[] [])) ⟩
  reverse (map mirror [])
    ≡⟨ reverseCong (map-[] mirror) ⟩
  reverse []
    ≡⟨ rev-[] [] ⟩
  [] ∎

helper (fcons {t} {ts} Tt Fts) =
  reverse (map mirror (reverse (map mirror (t ∷ ts))))
    ≡⟨ reverseCong (mapCong₂ (reverseCong (map-∷ mirror t ts))) ⟩
  reverse (map mirror (reverse (mirror · t ∷ map mirror ts)))
    ≡⟨ reverseCong (mapCong₂
                     (ForestP.reverse-∷ (mirror-Tree Tt)
                                        (map-Forest mirror mirror-Tree Fts)))
    ⟩
  reverse (map mirror (reverse (map mirror ts) ++ (mirror · t ∷ [])))
    ≡⟨ reverseCong (ForestP.map-++
                     mirror
                     mirror-Tree
                       (reverse-Forest (map-Forest mirror mirror-Tree Fts))
                       (mirror · t ∷ [])) ⟩


  reverse (map mirror (reverse (map mirror ts)) ++
          (map mirror (mirror · t ∷ [])))
    ≡⟨ subst (λ x → (reverse (map mirror (reverse (map mirror ts)) ++
                                         (map mirror (mirror · t ∷ [])))) ≡ x)
             (ForestP.reverse-++
               (map-Forest mirror mirror-Tree
                           (reverse-Forest
                           (map-Forest mirror mirror-Tree Fts)))
               (map-Forest mirror mirror-Tree
                           (fcons (mirror-Tree Tt) fnil)))
             refl
    ⟩
  reverse (map mirror (mirror · t ∷ [])) ++
  reverse (map mirror (reverse (map mirror ts)))
    ≡⟨ subst (λ x → reverse (map mirror (mirror · t ∷ [])) ++ n₁ ≡
                    reverse x ++ n₁)
             (map-∷ mirror (mirror · t) [])
             refl
    ⟩
  reverse (mirror · (mirror · t) ∷ map mirror []) ++ n₁
    ≡⟨ subst (λ x → reverse (mirror · (mirror · t) ∷ map mirror []) ++ n₁ ≡
                    reverse (mirror · (mirror · t) ∷ x) ++ n₁)
             (map-[] mirror)
             refl
    ⟩
  reverse (mirror · (mirror · t) ∷ []) ++ n₁
    ≡⟨ ++-leftCong (reverse-[x]≡[x] (mirror · (mirror · t))) ⟩
  (mirror · (mirror · t) ∷ []) ++ n₁
    ≡⟨ ++-∷ (mirror · (mirror · t)) [] n₁ ⟩
  mirror · (mirror · t) ∷ [] ++ n₁
    ≡⟨ subst (λ x → mirror · (mirror · t) ∷ [] ++ n₁ ≡
                    mirror · (mirror · t) ∷ x)
             (++-leftIdentity n₁)
             refl
    ⟩
  mirror · (mirror · t) ∷ reverse (map mirror (reverse (map mirror ts)))
    ≡⟨ ∷-leftCong (mirror-involutive Tt) ⟩
  t ∷ reverse (map mirror (reverse (map mirror ts)))
    ≡⟨ ∷-rightCong (helper Fts) ⟩
  t ∷ ts ∎
  where
  n₁ : D
  n₁ = reverse (map mirror (reverse (map mirror ts)))

  Fn₁ : Forest n₁
  Fn₁ = rev-Forest
          (map-Forest mirror mirror-Tree
                      (reverse-Forest (map-Forest mirror mirror-Tree Fts)))
          fnil
