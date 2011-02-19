------------------------------------------------------------------------------
-- Properties of the mirror function
------------------------------------------------------------------------------

module Draft.Mirror.PropertiesI where

open import LTC.Base

open import Draft.Mirror.Mirror
open import Draft.Mirror.ListTree.PropertiesI

open import LTC.Data.List
open import LTC.Data.List.PropertiesI using ( reverse-[x]≡[x] )
open import Draft.Mirror.ListTree.PropertiesI

open import LTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

-- TODO: To remove the postulate
postulate
  mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)

-- mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)
-- mirror-Tree (treeT d nilLT) =
--   subst Tree (sym (mirror-eq d [])) (treeT d aux₂)
--     where
--       aux₁ : rev (map mirror []) [] ≡ []
--       aux₁ =
--         begin
--           rev (map mirror []) []
--           ≡⟨ subst (λ x → rev (map mirror []) [] ≡ rev x [])
--                    (map-[] mirror)
--                    refl
--           ⟩
--           rev [] []
--             ≡⟨ rev-[] [] ⟩
--           []
--         ∎

--       aux₂ : ListTree (rev (map mirror []) [])
--       aux₂ = subst ListTree (sym aux₁) nilLT

-- mirror-Tree (treeT d (consLT {t} {ts} Tt LTts)) =
--   subst Tree (sym (mirror-eq d (t ∷ ts))) (treeT d aux)

--   where
--     aux : ListTree (reverse (map mirror (t ∷ ts)))
--     aux = rev-ListTree (map-ListTree mirror {!!} (consLT Tt LTts)) nilLT

mutual
  mirror² : ∀ {t} → Tree t → mirror · (mirror · t) ≡ t
  mirror² (treeT d nilLT) =
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

  mirror² (treeT d (consLT {t} {ts} Tt LTts)) =
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
               (helper (consLT Tt LTts))
               refl
      ⟩
      node d (t ∷ ts)
    ∎

  helper : ∀ {ts} → ListTree ts →
           reverse (map mirror (reverse (map mirror ts))) ≡ ts
  helper nilLT =
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

  helper (consLT {t} {ts} Tt LTts) =
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
                 (reverse-∷ (mirror · t) (map-ListTree mirror mirror-Tree LTts))
                 refl
        ⟩
      reverse (map mirror (reverse (map mirror ts) ++ (mirror · t ∷ [])))
        ≡⟨ subst (λ x → (reverse (map mirror (reverse (map mirror ts) ++
                                              mirror · t ∷ []))) ≡
                        reverse x)
           (map-++-commute mirror
                   mirror-Tree
                   (rev-ListTree (map-ListTree mirror mirror-Tree LTts) nilLT)
                   (consLT (mirror-Tree Tt) nilLT))
           refl
        ⟩
      reverse (map mirror (reverse (map mirror ts)) ++
              (map mirror (mirror · t ∷ [])))
        ≡⟨ subst (λ x → (reverse (map mirror (reverse (map mirror ts)) ++
                                             (map mirror (mirror · t ∷ [])))) ≡
                        x)
                 (reverse-++-commute (map-ListTree mirror
                                           mirror-Tree
                                           (rev-ListTree (map-ListTree mirror
                                                                       mirror-Tree
                                                                       LTts)
                                                         nilLT))
                             (map-ListTree mirror
                                           mirror-Tree
                                           (consLT (mirror-Tree Tt) nilLT)))
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
                 (++-leftIdentity LTn₁)
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
                 (helper LTts)
                 refl
        ⟩
      t ∷ ts
    ∎
      where
        n₁ : D
        n₁ = reverse (map mirror (reverse (map mirror ts)))

        LTn₁ : ListTree n₁
        LTn₁ = rev-ListTree (map-ListTree mirror
                                          mirror-Tree
                                          (rev-ListTree (map-ListTree mirror
                                                                      mirror-Tree
                                                                      LTts)
                                                        nilLT))
                            nilLT
