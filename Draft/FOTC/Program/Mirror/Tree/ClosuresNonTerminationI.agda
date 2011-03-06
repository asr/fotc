------------------------------------------------------------------------------
-- Properties related with the closures of the rose tree type
------------------------------------------------------------------------------

-- {-# OPTIONS --no-termination-check #-}
{-# OPTIONS --injective-type-constructors #-}

module Draft.FOTC.Program.Mirror.Tree.ClosuresNonTerminationI where

open import FOTC.Base

open import FOTC.Data.List

open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.Type
open import FOTC.Program.Mirror.Forest.Closures
open import FOTC.Program.Mirror.Forest.PropertiesI

open import FOTC.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

-- Requires --injective-type-constructors
-- Peter: To use injectivity of type constructors means asking for
-- trouble. The logic behind this is very unclear.
node-Forest : ∀ {d ts} → Tree (node d ts) → Forest ts
node-Forest {d} (treeT .d Fts) = Fts

postulate
  reverse-∷' : ∀ x ys → reverse (x ∷ ys) ≡ reverse ys ++ (x ∷ [])

-- Andreas Abel: The function does not terminate because we are using
-- postulates (i.e. D, _∷_, etc). In particular, x is not structurally
-- smaller than x ∷ xs.

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
     h₁ : Tree (node d (reverse (map mirror ts)))
     h₁ = subst Tree (mirror-eq d ts) (mirror-Tree (treeT d Fts))

     h₂ : Forest (reverse (map mirror ts))
     h₂ = node-Forest h₁

     h₃ : Forest ((reverse (map mirror ts)) ++ (mirror · t ∷ []))
     h₃ = ++-Forest h₂ (consF (mirror-Tree Tt) nilF)

     h₄ : Forest (reverse (mirror · t ∷ map mirror ts))
     h₄ = subst Forest ( sym (reverse-∷' (mirror · t) (map mirror ts))) h₃

     helper : Forest (reverse (map mirror (t ∷ ts)))
     helper = subst Forest
              (subst (λ x → reverse x ≡ reverse (map mirror (t ∷ ts)))
                     (map-∷ mirror t ts)
                     refl)
              h₄
