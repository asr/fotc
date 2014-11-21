------------------------------------------------------------------------------
-- Well-founded induction on the relation TreeT
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Program.Mirror.TreeR.Induction.Acc.WellFoundedInduction
  where

open import FOTC.Base

open import FOT.FOTC.Program.Mirror.Induction.Acc.WellFounded
open import FOT.FOTC.Program.Mirror.TreeR
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------
-- The relation TreeR is well-founded.
postulate wf-TreeR : WellFounded TreeR

-- Well-founded induction on the relation TreeT.
wfInd-TreeR :
  (P : D → Set) →
  (∀ {t} → Tree t → (∀ {t'} → Tree t' → TreeR t' t → P t') → P t) →
  ∀ {t} → Tree t → P t
wfInd-TreeR P = WellFoundedInduction wf-TreeR
