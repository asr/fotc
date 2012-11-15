------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Induction.Acc.WF-I where

open import FOTC.Base
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.EliminationProperties
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.Type
open import FOTC.Induction.WF

------------------------------------------------------------------------------
-- The relation _<_ is well-founded.
module <-WF where
  <-wf : WellFounded _<_
  <-wf Nn = acc (helper Nn)
    where
    -- N.B. The helper function is the same that the function used by
    -- FOTC.Data.Nat.Induction.NonAcc.WellFoundedInductionATP.
    helper : ∀ {n m} → N n → N m → m < n → Acc N _<_ m
    helper nzero Nm m<0  = ⊥-elim (x<0→⊥ Nm m<0)
    helper (nsucc _) nzero 0<Sn = acc (λ Nm' m'<0 → ⊥-elim (x<0→⊥ Nm' m'<0))
    helper (nsucc {n} Nn) (nsucc {m} Nm) Sm<Sn =
      acc (λ {m'} Nm' m'<Sm →
             let m<n : m < n
                 m<n = Sx<Sy→x<y Sm<Sn

                 m'<n : m' < n
                 m'<n = case (λ m'<m → <-trans Nm' Nm Nn m'<m m<n)
                             (λ m'≡m → x≡y→y<z→x<z m'≡m m<n)
                             (x<Sy→x<y∨x≡y Nm' Nm m'<Sm)

             in  helper Nn Nm' m'<n
          )

  -- Well-founded induction on the natural numbers.
  <-wfind : (A : D → Set) →
             (∀ {n} → N n → (∀ {m} → N m → m < n → A m) → A n) →
             ∀ {n} → N n → A n
  <-wfind A = WellFoundedInduction <-wf

------------------------------------------------------------------------------
-- The relation _<_ is well-founded (a different proof).
module <-WF' where

  <-wf : WellFounded {N} _<_
  <-wf nzero      = acc (λ Nm m<0 → ⊥-elim (x<0→⊥ Nm m<0))
  <-wf (nsucc Nn) = acc (λ Nm m<Sn → helper Nm Nn (<-wf Nn)
                                          (x<Sy→x≤y Nm Nn m<Sn))
    where
    helper : ∀ {n m} → N n → N m → Acc N _<_ m → n ≤ m → Acc N _<_ n
    helper {n} {m} Nn Nm (acc h) n≤m = case (λ n<m → h Nn n<m)
                                            (λ n≡m → helper₁ (sym n≡m) (acc h))
                                            (x≤y→x<y∨x≡y Nn Nm n≤m)
      where
      helper₁ : ∀ {a b} → a ≡ b → Acc N _<_ a → Acc N _<_ b
      helper₁ a≡b acc-a = subst (Acc N _<_) a≡b acc-a
