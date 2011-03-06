module Draft.FOTC.Program.Mirror.Other.StructurallySmaller where

open import FOTC.Base
open import FOTC.Program.Mirror.Type

foo : ∀ {ts} → Tree ts → D
foo (treeT d nilF)            = d
foo (treeT d (consF Tt Fts)) = foo (treeT d Fts)

bar : ∀ {ts} → Tree ts → D
bar (treeT d nilF) = d
bar (treeT d (consF Tt Fts)) = helper (bar Tt) (bar (treeT d Fts))
  where
    postulate helper : D → D → D

bar₁ : ∀ ts → Tree ts → D
bar₁ .(node d [])       (treeT d nilF) = d
bar₁ .(node d (t ∷ ts)) (treeT d (consF {t} {ts} Tt Fts))
  = helper (bar₁ t Tt) (bar₁ (node d ts) (treeT d Fts))
  where
    postulate helper : D → D → D
