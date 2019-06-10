------------------------------------------------------------------------------
-- Well-founded induction on the relation TreeT
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Program.Mirror.TreeR.Induction.Acc.WellFoundedInduction
  where

open import Interactive.FOTC.Base

open import InteractiveFOT.FOTC.Program.Mirror.Induction.Acc.WellFounded
open import InteractiveFOT.FOTC.Program.Mirror.TreeR

open import Interactive.FOTC.Program.Mirror.Type

------------------------------------------------------------------------------
-- The relation TreeR is well-founded.
postulate wf-TreeR : WellFounded TreeR

-- Well-founded induction on the relation TreeT.
wfInd-TreeR :
  (P : D → Set) →
  (∀ {t} → Tree t → (∀ {t'} → Tree t' → TreeR t' t → P t') → P t) →
  ∀ {t} → Tree t → P t
wfInd-TreeR P = WellFoundedInduction wf-TreeR
