------------------------------------------------------------------------------
-- Well-founded induction on the relation TreeT
------------------------------------------------------------------------------

module Draft.FOTC.Program.Mirror.TreeR.Induction.Acc.WellFoundedInduction
       where

open import FOTC.Base

open import Draft.FOTC.Program.Mirror.Induction.Acc.WellFounded
open import FOTC.Program.Mirror.Type
open import Draft.FOTC.Program.Mirror.TreeR

------------------------------------------------------------------------------
-- The relation TreeR is well-founded.
postulate
  wf-TreeR : WellFounded TreeR

-- Well-founded induction on the relation TreeT.
wfInd-TreeR :
  (P : D → Set) →
  (∀ {t} → Tree t → (∀ {t'} → Tree t' → TreeR t' t → P t') → P t) →
  ∀ {t} → Tree t → P t
wfInd-TreeR P = WellFoundedInduction wf-TreeR
