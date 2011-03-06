------------------------------------------------------------------------------
-- Properties related with the closures of the rose tree type
------------------------------------------------------------------------------

{-# OPTIONS --no-termination-check #-}

module FOTC.Program.Mirror.Tree.ClosuresI where

open import FOTC.Base

open import FOTC.Data.List

open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.Forest.Closures
open import FOTC.Program.Mirror.Type

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)
mirror-Tree (treeT d nilF) =
  subst Tree (sym (mirror-eq d [])) (treeT d helper₂)
    where
      helper₁ : rev (map mirror []) [] ≡ []
      helper₁ =
        begin
          rev (map mirror []) []
          ≡⟨ subst (λ x → rev (map mirror []) [] ≡ rev x [])
                   (map-[] mirror)
                   refl
          ⟩
          rev [] []
            ≡⟨ rev-[] [] ⟩
          []
        ∎

      helper₂ : Forest (rev (map mirror []) [])
      helper₂ = subst Forest (sym helper₁) nilF

mirror-Tree (treeT d (consF {t} {ts} Tt Fts)) =
  subst Tree (sym (mirror-eq d (t ∷ ts))) (treeT d helper)

  where
    helper : Forest (reverse (map mirror (t ∷ ts)))
    helper = reverse-Forest (map-Forest mirror mirror-Tree (consF Tt Fts))
