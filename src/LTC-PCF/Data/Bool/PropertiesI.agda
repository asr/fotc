------------------------------------------------------------------------------
-- The Booleans properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Bool.PropertiesI where

open import LTC-PCF.Base
open import LTC-PCF.Data.Bool
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI
open import LTC-PCF.Data.Nat.Type

------------------------------------------------------------------------------
-- Properties with inequalities

<-Bool : ∀ {m n} → N m → N n → Bool (m < n)
<-Bool zN          zN          = subst Bool (sym <-00) fB
<-Bool zN          (sN {n} Nn) = subst Bool (sym (<-0S n)) tB
<-Bool (sN {m} Nm) zN          = subst Bool (sym (<-S0 m)) fB
<-Bool (sN {m} Nm) (sN {n} Nn) = subst Bool (sym (<-SS m n)) (<-Bool Nm Nn)

≤-Bool : ∀ {m n} → N m → N n → Bool (m ≤ n)
≤-Bool {n = n} zN         Nn          = subst Bool (sym (<-0S n)) tB
≤-Bool        (sN Nm)     zN          = subst Bool (sym (Sx≰0 Nm)) fB
≤-Bool        (sN {m} Nm) (sN {n} Nn) =
  subst Bool (sym (<-SS m (succ₁ n))) (≤-Bool Nm Nn)
