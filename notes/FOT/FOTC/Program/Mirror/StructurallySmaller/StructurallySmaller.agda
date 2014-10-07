{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Program.Mirror.StructurallySmaller.StructurallySmaller where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

{-# TERMINATING #-}
foo : ∀ {ts} → Tree ts → D
foo (tree d fnil)           = d
foo (tree d (fcons Tt Fts)) = foo (tree d Fts)

{-# TERMINATING #-}
bar : ∀ {ts} → Tree ts → D
bar (tree d fnil)           = d
bar (tree d (fcons Tt Fts)) = helper (bar Tt) (bar (tree d Fts))
  where
  postulate helper : D → D → D

{-# TERMINATING #-}
bar₁ : ∀ ts → Tree ts → D
bar₁ .(node d []) (tree d fnil) = d
bar₁ .(node d (t ∷ ts)) (tree d (fcons {t} {ts} Tt Fts))
  = helper (bar₁ t Tt) (bar₁ (node d ts) (tree d Fts))
  where
  postulate helper : D → D → D
