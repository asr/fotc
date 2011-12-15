------------------------------------------------------------------------------
-- Properties of the mirror function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Mirror.PropertiesI where

open import FOTC.Base
open import FOTC.Data.List
open import FOTC.Data.List.PropertiesI using ( reverse-[x]≡[x] )
open import FOTC.Program.Mirror.Type
open import FOTC.Program.Mirror.Forest.PropertiesI
open import FOTC.Program.Mirror.Forest.Totality
open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.Tree.Totality
open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

mutual
  mirror² : ∀ {t} → Tree t → mirror · (mirror · t) ≡ t
  mirror² (treeT d nilF) =
    begin
      mirror · (mirror · (node d []))
        ≡⟨ subst (λ x → mirror · (mirror · (node d [])) ≡ mirror · x )
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
        ≡⟨ subst (λ x → node d (reverse []) ≡ node d x)
                 (rev-[] [])
                 refl
        ⟩
      node d []
    ∎

  mirror² (treeT d (consF {t} {ts} Tt Fts)) =
    begin
      mirror · (mirror · node d (t ∷ ts))
        ≡⟨ subst (λ x → mirror · (mirror · node d (t ∷ ts)) ≡ mirror · x)
                 (mirror-eq d (t ∷ ts))
                 refl
        ⟩
      mirror · node d (reverse (map mirror (t ∷ ts)))
        ≡⟨ subst (λ x → mirror · node d (reverse (map mirror (t ∷ ts))) ≡
                        x)
                 (mirror-eq d (reverse (map mirror (t ∷ ts))))
                 refl
        ⟩
      node d (reverse (map mirror (reverse (map mirror (t ∷ ts)))))
      ≡⟨ subst (λ x → node d (reverse (map mirror (reverse (map mirror (t ∷ ts))))) ≡
                      node d x)
               (helper (consF Tt Fts))
               refl
      ⟩
      node d (t ∷ ts)
    ∎

  helper : ∀ {ts} → Forest ts →
           reverse (map mirror (reverse (map mirror ts))) ≡ ts
  helper nilF =
    begin
      reverse (map mirror (reverse (map mirror [])))
        ≡⟨ subst (λ x → reverse (map mirror (reverse (map mirror []))) ≡
                        reverse (map mirror (reverse x)))
                 (map-[] mirror)
                 refl
        ⟩
      reverse (map mirror (reverse []))
        ≡⟨ subst (λ x → reverse (map mirror (reverse [])) ≡
                        reverse (map mirror x))
                 (rev-[] [])
                 refl
        ⟩
      reverse (map mirror [])
        ≡⟨ subst (λ x → reverse (map mirror []) ≡
                        reverse x)
                 (map-[] mirror)
                 refl
        ⟩
      reverse []
        ≡⟨ rev-[] [] ⟩
      []
    ∎

  helper (consF {t} {ts} Tt Fts) =
    begin
      reverse (map mirror (reverse (map mirror (t ∷ ts))))
        ≡⟨ subst (λ x → reverse (map mirror (reverse (map mirror (t ∷ ts)))) ≡
                        reverse (map mirror (reverse x)))
                 (map-∷ mirror t ts)
                 refl
        ⟩
      reverse (map mirror (reverse (mirror · t ∷ map mirror ts)))
        ≡⟨ subst (λ x → reverse (map mirror (reverse (mirror · t ∷ map mirror ts))) ≡
                        reverse (map mirror x))
                 (reverse-∷ (mirror-Tree Tt) (map-Forest mirror mirror-Tree Fts))
                 refl
        ⟩
      reverse (map mirror (reverse (map mirror ts) ++ (mirror · t ∷ [])))
        ≡⟨ subst (λ x → (reverse (map mirror (reverse (map mirror ts) ++
                                              mirror · t ∷ []))) ≡
                        reverse x)
           (map-++-commute mirror
                   mirror-Tree
                   (reverse-Forest (map-Forest mirror mirror-Tree Fts))
                   (consF (mirror-Tree Tt) nilF))
           refl
        ⟩
      reverse (map mirror (reverse (map mirror ts)) ++
              (map mirror (mirror · t ∷ [])))
        ≡⟨ subst (λ x → (reverse (map mirror (reverse (map mirror ts)) ++
                                             (map mirror (mirror · t ∷ [])))) ≡
                        x)
                 (reverse-++-commute
                   (map-Forest mirror mirror-Tree
                               (reverse-Forest
                               (map-Forest mirror mirror-Tree Fts)))
                   (map-Forest mirror mirror-Tree
                               (consF (mirror-Tree Tt) nilF)))
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
        ≡⟨ subst (λ x → reverse (mirror · (mirror · t) ∷ []) ++ n₁ ≡
                        x ++ n₁)
                 (reverse-[x]≡[x] (mirror · (mirror · t)))
                 refl
        ⟩
      (mirror · (mirror · t) ∷ []) ++ n₁
        ≡⟨ ++-∷ (mirror · (mirror · t)) [] n₁ ⟩
      mirror · (mirror · t) ∷ [] ++ n₁
        ≡⟨ subst (λ x →  mirror · (mirror · t) ∷ [] ++ n₁ ≡
                         mirror · (mirror · t) ∷ x)
                 (++-leftIdentity Fn₁)
                 refl
        ⟩
      mirror · (mirror · t) ∷ reverse (map mirror (reverse (map mirror ts)))
        ≡⟨ subst (λ x → (mirror · (mirror · t) ∷
                                reverse (map mirror (reverse (map mirror ts)))) ≡
                        (x ∷ reverse (map mirror (reverse (map mirror ts)))))
                 (mirror² Tt)  -- IH.
                 refl
        ⟩
      t ∷ reverse (map mirror (reverse (map mirror ts)))
        ≡⟨ subst (λ x → t ∷ reverse (map mirror (reverse (map mirror ts))) ≡
                        t ∷ x)
                 (helper Fts)
                 refl
        ⟩
      t ∷ ts
    ∎
      where
      n₁ : D
      n₁ = reverse (map mirror (reverse (map mirror ts)))

      Fn₁ : Forest n₁
      Fn₁ = rev-Forest
            (map-Forest mirror mirror-Tree
                        (reverse-Forest (map-Forest mirror mirror-Tree Fts)))
            nilF
