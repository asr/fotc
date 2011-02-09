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

-- TODO: To remove
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
                      mirror · node d (reverse x))
               (map-∷ mirror t ts)
               refl
      ⟩
    mirror · node d (reverse (mirror · t ∷ map mirror ts))
      ≡⟨ subst (λ x → mirror · node d (reverse (mirror · t ∷ map mirror ts)) ≡
                      mirror · node d x)
               (reverse-∷ (mirror · t) (map-ListTree mirror mirror-Tree LTts))
               refl
      ⟩
    mirror · node d (reverse (map mirror ts) ++ (mirror · t ∷ []))
      ≡⟨ mirror-eq d (reverse (map mirror ts) ++ (mirror · t ∷ [])) ⟩
    node d (reverse (map mirror (reverse (map mirror ts) ++ (mirror · t ∷ []))))
      ≡⟨ subst (λ x → node d (reverse (map mirror (reverse (map mirror ts) ++
                                      (mirror · t ∷ [])))) ≡
                      node d (reverse x))
               (map-++ mirror
                       mirror-Tree
                       (rev-ListTree (map-ListTree mirror mirror-Tree LTts) nilLT)
                       (consLT (mirror-Tree Tt) nilLT))
               refl
      ⟩
    node d (reverse ((map mirror (reverse (map mirror ts))) ++
                      map mirror (mirror · t ∷ [])))
      ≡⟨ subst (λ x → node d (reverse ((map mirror (reverse (map mirror ts))) ++
                      map mirror (mirror · t ∷ []))) ≡
                      node d x)
               (reverse-++ (map-ListTree mirror
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
    node d (reverse (map mirror (mirror · t ∷ [])) ++
            reverse (map mirror (reverse (map mirror ts))))
      ≡⟨ subst (λ x → node d (reverse (map mirror (mirror · t ∷ [])) ++
                             reverse (map mirror (reverse (map mirror ts)))) ≡
                      node d (reverse x ++
                             reverse (map mirror (reverse (map mirror ts)))))
               (map-∷ mirror (mirror · t) [])
               refl
      ⟩
    node d (reverse (mirror · (mirror · t) ∷ map mirror []) ++
            reverse (map mirror (reverse (map mirror ts))))
      ≡⟨ subst (λ x → node d (reverse (mirror · (mirror · t) ∷ map mirror []) ++
                              reverse (map mirror (reverse (map mirror ts)))) ≡
                      node d (reverse (x ∷ map mirror []) ++
                             reverse (map mirror (reverse (map mirror ts)))))
               (mirror² Tt)  -- IH.
               refl
      ⟩
    node d (reverse (t ∷ map mirror []) ++
            reverse (map mirror (reverse (map mirror ts))))
      ≡⟨ subst (λ x → node d (reverse (t ∷ map mirror []) ++
                              reverse (map mirror (reverse (map mirror ts)))) ≡
                      node d (reverse (t ∷ x) ++
                              reverse (map mirror (reverse (map mirror ts)))))
               (map-[] mirror)
               refl
      ⟩
    node d (reverse (t ∷ []) ++
            reverse (map mirror (reverse (map mirror ts))))
      ≡⟨ subst (λ x → node d (reverse (t ∷ []) ++
                              reverse (map mirror (reverse (map mirror ts)))) ≡
                      node d (x ++
                              reverse (map mirror (reverse (map mirror ts)))))
               (reverse-[x]≡[x] t)
               refl
      ⟩
    node d ((t ∷ []) ++
            reverse (map mirror (reverse (map mirror ts))))
      ≡⟨ subst (λ x → node d ((t ∷ []) ++
                              reverse (map mirror (reverse (map mirror ts)))) ≡
                      node d ((t ∷ []) ++ x))
               (prf (mirror² {!!}))
               refl
      ⟩
    node d ((t ∷ []) ++ ts)
      ≡⟨ subst (λ x → node d ((t ∷ []) ++ ts) ≡ node d x)
               (++-∷ t [] ts)
               refl
      ⟩
    node d (t ∷ [] ++ ts)
      ≡⟨ subst (λ x → node d (t ∷ [] ++ ts) ≡ node d (t ∷ x))
               (++-leftIdentity LTts)
               refl
      ⟩
    node d (t ∷ ts)
  ∎
  where
    postulate prf : mirror · (mirror · ts) ≡ ts →  -- IH
                    rev (map mirror (rev (map mirror ts) [])) [] ≡ ts
    {-# ATP prove prf #-}
