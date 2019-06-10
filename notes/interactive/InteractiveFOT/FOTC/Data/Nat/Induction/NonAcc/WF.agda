----------------------------------------------------------------------------
-- Well-founded induction on the natural numbers
----------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas     #-}
{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Data.Nat.Induction.NonAcc.WF where

open import Interactive.FOTC.Base

open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.Inequalities.EliminationProperties
open import Interactive.FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Well-founded induction
postulate
  <-wfind₁ : (A : D → Set) →
             (∀ {n} → N n → (∀ {m} → N m → m < n → A m) → A n) →
             ∀ {n} → N n → A n

postulate PN : ∀ {n m} → N n → m < n → N m

-- Well-founded induction removing N m from the second line.
<-wfind₂ : (A : D → Set) →
           (∀ {n} → N n → (∀ {m} → m < n → A m) → A n) →
           ∀ {n} → N n → A n
<-wfind₂ A h = <-wfind₁ A (λ Nn' h' → h Nn' (λ p → h' (PN Nn' p) p))

-- Well-founded induction removing N n from the second line.
<-wfind₃ : (A : D → Set) →
           (∀ {n} → (∀ {m} → N m → m < n → A m) → A n) →
           ∀ {n} → N n → A n
<-wfind₃ A h = <-wfind₁ A (λ Nn' h' → h h')
