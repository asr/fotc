------------------------------------------------------------------------------
-- Properties related with the closures of the tree type
------------------------------------------------------------------------------

module Draft.Mirror.Tree.Closures where

open import LTC.Base

open import Draft.Mirror.Mirror

open import LTC.Data.List

------------------------------------------------------------------------------

-- TODO: To remove the postulate
postulate
  mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)

-- mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)
-- mirror-Tree (treeT d nilLT) =
--   subst Tree (sym (mirror-eq d [])) (treeT d helper₂)
--     where
--       helper₁ : rev (map mirror []) [] ≡ []
--       helper₁ =
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

--       helper₂ : ListTree (rev (map mirror []) [])
--       helper₂ = subst ListTree (sym helper₁) nilLT

-- mirror-Tree (treeT d (consLT {t} {ts} Tt LTts)) =
--   subst Tree (sym (mirror-eq d (t ∷ ts))) (treeT d helper)

--   where
--     helper : ListTree (reverse (map mirror (t ∷ ts)))
--     helper = rev-ListTree (map-ListTree mirror {!!} (consLT Tt LTts)) nilLT
