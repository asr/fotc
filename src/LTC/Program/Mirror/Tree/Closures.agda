------------------------------------------------------------------------------
-- Properties related with the closures of the tree type
------------------------------------------------------------------------------

{-# OPTIONS --no-termination-check #-}

module LTC.Program.Mirror.Tree.Closures where

open import LTC.Base

open import LTC.Data.List

open import LTC.Program.Mirror.Mirror
open import LTC.Program.Mirror.ListTree.Closures

open import LTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)
mirror-Tree (treeT d nilLT) =
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

      helper₂ : ListTree (rev (map mirror []) [])
      helper₂ = subst ListTree (sym helper₁) nilLT

mirror-Tree (treeT d (consLT {t} {ts} Tt LTts)) =
  subst Tree (sym (mirror-eq d (t ∷ ts))) (treeT d helper)

  where
    helper : ListTree (reverse (map mirror (t ∷ ts)))
    helper = reverse-ListTree (map-ListTree mirror mirror-Tree (consLT Tt LTts))
