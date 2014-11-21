----------------------------------------------------------------------------
-- Well-founded induction on the relation _◁_
----------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module FOT.FOTC.Program.McCarthy91.WF-Relation.Induction.NonAcc.WellFoundedATP
  where

open import FOTC.Base

open import FOTC.Data.Nat

open import FOTC.Program.McCarthy91.McCarthy91
open import FOTC.Program.McCarthy91.WF-Relation
open import FOTC.Program.McCarthy91.WF-Relation.PropertiesATP

----------------------------------------------------------------------------
-- Adapted from FOTC.Data.Nat.Induction.WellFoundedI.wfInd-LT₁.

{-# TERMINATING #-}
◁-wfind : (P : D → Set) →
          (∀ {n} → N n → (∀ {m} → N m → m ◁ n → P m) → P n) →
          ∀ {n} → N n → P n
◁-wfind P h Nn = h Nn (helper Nn)
  where
    helper : ∀ {n m} → N n → N m → m ◁ n → P m
    helper Nn nzero 0◁n = ⊥-elim (0◁x→⊥ Nn 0◁n)

    -- This equation does not pass the termination check.
    helper nzero (nsucc Nm) Sm◁0 = h (nsucc Nm)
      (λ {m'} Nm' m'◁Sm →
        let m'◁0 : m' ◁ zero
            m'◁0 = ◁-trans Nm' (nsucc Nm) nzero m'◁Sm Sm◁0

        in helper nzero Nm' m'◁0
      )

    -- Other version of the previous equation (this version neither
    -- pass the termination check).
    -- helper nzero (nsucc {m} Nm) Sm◁0 = h (nsucc Nm)
    --   (λ {m'} Nm' m'◁Sm →
    --     let m'◁m : MCR m' m
    --         m'◁m = x◁Sy→x◁y Nm' Nm m'◁Sm

    --     in helper Nm Nm' m'◁m
    --   )

    -- Other version of the previous equation (this version neither
    -- pass the termination check).
    -- helper nzero Nm m◁0 = h Nm
    --   (λ {m'} Nm' m'◁m →
    --     let m'◁0 : MCR m' zero
    --         m'◁0 = ◁-trans Nm' Nm nzero m'◁m m◁0

    --     in helper nzero Nm' m'◁0
    --   )

    -- Other version of the previous equation (this version neither
    -- pass the termination check).
    -- helper {m = m} nzero Nm m◁0 =
    --   h Nm (λ {m'} Nm' m'◁m → helper Nm Nm' m'◁m)

    helper (nsucc {n} Nn) (nsucc {m} Nm) Sm◁Sn = helper Nn (nsucc Nm) Sm◁n
      where
        Sm◁n : succ₁ m ◁ n
        Sm◁n = x◁Sy→x◁y (nsucc Nm) Nn Sm◁Sn
