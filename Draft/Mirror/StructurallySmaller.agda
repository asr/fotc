module Draft.Mirror.StructurallySmaller where

open import FOTC.Base
open import FOTC.Program.Mirror.Mirror

foo : ∀ {ts} → Tree ts → D
foo (treeT d nilLT)            = d
foo (treeT d (consLT Tt LTts)) = foo (treeT d LTts)
