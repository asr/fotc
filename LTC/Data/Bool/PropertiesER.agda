------------------------------------------------------------------------------
-- The booleans properties
------------------------------------------------------------------------------

module LTC.Data.Bool.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER using ( subst )
open import LTC.Data.Bool
open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesER using ( le-SS ; S≰0 )

------------------------------------------------------------------------------
-- Basic properties.

&&-Bool : {b₁ b₂ : D} → Bool b₁ → Bool b₂ → Bool (b₁ && b₂)
&&-Bool tB tB = subst (λ t → Bool t) (sym &&-tt) tB
&&-Bool tB fB = subst (λ t → Bool t) (sym &&-tf) fB
&&-Bool fB tB = subst (λ t → Bool t) (sym &&-ft) fB
&&-Bool fB fB = subst (λ t → Bool t) (sym &&-ff) fB

x&&y≡true→x≡true : {b₁ b₂ : D} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ true →
                   b₁ ≡ true
x&&y≡true→x≡true tB _ _    = refl
x&&y≡true→x≡true fB tB prf = ⊥-elim (true≠false (trans (sym prf) &&-ft))
x&&y≡true→x≡true fB fB prf = ⊥-elim (true≠false (trans (sym prf) &&-ff))

x&&y≡true→y≡true : {b₁ b₂ : D} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ true →
                   b₂ ≡ true
x&&y≡true→y≡true _  tB _   = refl
x&&y≡true→y≡true tB fB prf = ⊥-elim (true≠false (trans (sym prf) &&-tf))
x&&y≡true→y≡true fB fB prf = ⊥-elim (true≠false (trans (sym prf) &&-ff))

------------------------------------------------------------------------------
-- Properties with inequalities

le-Bool : {m n : D} → N m → N n → Bool (le m n)
le-Bool {n = n} zN Nn           = subst (λ t → Bool t) (sym (lt-0S n)) tB
le-Bool (sN Nm) zN              = subst (λ t → Bool t) (sym (S≰0 Nm)) fB
le-Bool (sN {m} Nm) (sN {n} Nn) = subst (λ t → Bool t)
                                        (sym (le-SS m n))
                                        (le-Bool Nm Nn)
