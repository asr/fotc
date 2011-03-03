module Draft.Mirror.StructurallySmaller where

open import FOTC.Base
open import FOTC.Program.Mirror.Mirror

foo : ∀ {ts} → Tree ts → D
foo (treeT d nilLT)            = d
foo (treeT d (consLT Tt LTts)) = foo (treeT d LTts)

bar : ∀ {ts} → Tree ts → D
bar (treeT d nilLT) = d
bar (treeT d (consLT Tt LTts)) = helper (bar Tt) (bar (treeT d LTts))
  where
    postulate helper : D → D → D

bar₁ : ∀ ts → Tree ts → D
bar₁ .(node d [])       (treeT d nilLT) = d
bar₁ .(node d (t ∷ ts)) (treeT d (consLT {t} {ts} Tt LTts))
  = helper (bar₁ t Tt) (bar₁ (node d ts) (treeT d LTts))
  where
    postulate helper : D → D → D
