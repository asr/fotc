------------------------------------------------------------------------------
-- Properties related with the closures of the tree type
------------------------------------------------------------------------------

-- {-# OPTIONS --no-termination-check #-}
{-# OPTIONS --injective-type-constructors #-}

module Draft.Mirror.Tree.ClosuresI where

open import FOTC.Base

open import FOTC.Data.List

open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.ListTree.Closures
open import FOTC.Program.Mirror.ListTree.PropertiesI

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

node-ListTree : ∀ {d ts} → Tree (node d ts) → ListTree ts
node-ListTree {d} (treeT .d LTts) = LTts

postulate
  reverse-∷' : ∀ x ys → reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])

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
     h₁ : Tree (node d (reverse (map mirror ts)))
     h₁ = subst Tree (mirror-eq d ts) (mirror-Tree (treeT d LTts))

     h₂ : ListTree (reverse (map mirror ts))
     h₂ = node-ListTree h₁

     h₃ : ListTree ((reverse (map mirror ts)) ++ (mirror · t ∷ []))
     h₃ = ++-ListTree h₂ (consLT (mirror-Tree Tt) nilLT)

     h₄ : ListTree (reverse (mirror · t ∷ map mirror ts))
     h₄ = subst ListTree ( sym (reverse-∷' (mirror · t) (map mirror ts))) h₃

     helper : ListTree (reverse (map mirror (t ∷ ts)))
     helper = subst ListTree
              (subst (λ x → reverse x ≡ reverse (map mirror (t ∷ ts)))
                     (map-∷ mirror t ts)
                     refl)
              h₄
