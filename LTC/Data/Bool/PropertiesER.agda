------------------------------------------------------------------------------
-- The booleans properties (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Data.Bool.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER using ( subst )

open import LTC.Data.Bool using
  ( _&&_ ; &&-ff ; &&-ft ; &&-tf ; &&-tt
  ; Bool ; fB ; tB
  )
open import LTC.Data.Nat.Inequalities using ( _≤_ ; <-0S )
open import LTC.Data.Nat.Inequalities.PropertiesER using ( ≤-SS ; S≰0 )
open import LTC.Data.Nat.Type using ( N ; sN ; zN )

import MyStdLib.Relation.Binary.EqReasoning
open module Bool-ER =
  MyStdLib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

------------------------------------------------------------------------------
-- Basic properties

&&-Bool : {b₁ b₂ : D} → Bool b₁ → Bool b₂ → Bool (b₁ && b₂)
&&-Bool tB tB = subst (λ t → Bool t) (sym &&-tt) tB
&&-Bool tB fB = subst (λ t → Bool t) (sym &&-tf) fB
&&-Bool fB tB = subst (λ t → Bool t) (sym &&-ft) fB
&&-Bool fB fB = subst (λ t → Bool t) (sym &&-ff) fB

x&&false≡false : {b : D} → Bool b → b && false ≡ false
x&&false≡false tB = &&-tf
x&&false≡false fB = &&-ff

false&&x≡false : {b : D} → Bool b → false && b ≡ false
false&&x≡false tB = &&-ft
false&&x≡false fB = &&-ff

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

w&&x&&y&&z≡true→y≡true : {b₁ b₂ b₃ b₄ : D} →
                         Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
                         b₁ && b₂ && b₃ && b₄ ≡ true →
                         b₃ ≡ true
w&&x&&y&&z≡true→y≡true Bb₁ Bb₂ tB Bb₄ b₁&&b₂&&b₃&&b₄≡true = refl
w&&x&&y&&z≡true→y≡true {b₁} {b₂} {b₄ = b₄} Bb₁ Bb₂ fB Bb₄ b₁&&b₂&&b₃&&b₄≡true =
  ⊥-elim (true≠false (trans (sym b₁&&b₂&&b₃&&b₄≡true)
                            ( begin
                                b₁ && b₂ && false && b₄
                                  ≡⟨ subst (λ t → b₁ && b₂ && false && b₄ ≡
                                                  b₁ && b₂ && t)
                                           (false&&x≡false Bb₄)
                                           refl ⟩
                                b₁ && b₂ && false
                                  ≡⟨ subst (λ t → b₁ && b₂ && false ≡ b₁ && t)
                                           (x&&false≡false Bb₂)
                                           refl
                                  ⟩
                                b₁ && false
                                  ≡⟨ x&&false≡false Bb₁ ⟩
                                false
                              ∎
                            )))


w&&x&&y&&z≡true→z≡true : {b₁ b₂ b₃ b₄ : D} →
                         Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
                         b₁ && b₂ && b₃ && b₄ ≡ true →
                         b₄ ≡ true
w&&x&&y&&z≡true→z≡true Bb₁ Bb₂ Bb₃ tB b₁&&b₂&&b₃&&b₄≡true = refl
w&&x&&y&&z≡true→z≡true {b₁} {b₂} {b₃} Bb₁ Bb₂ Bb₃ fB
                       b₁&&b₂&&b₃&&b₄≡true =
  ⊥-elim (true≠false (trans (sym b₁&&b₂&&b₃&&b₄≡true)
                            ( begin
                                b₁ && b₂ && b₃ && false
                                  ≡⟨ subst (λ t → b₁ && b₂ && b₃ && false ≡
                                                  b₁ && b₂ && t)
                                           (x&&false≡false Bb₃)
                                           refl ⟩
                                b₁ && b₂ && false
                                  ≡⟨ subst (λ t → b₁ && b₂ && false ≡ b₁ && t)
                                           (x&&false≡false Bb₂)
                                           refl
                                  ⟩
                                b₁ && false
                                  ≡⟨ x&&false≡false Bb₁ ⟩
                                false
                              ∎
                            )))

------------------------------------------------------------------------------
-- Properties with inequalities

≤-Bool : {m n : D} → N m → N n → Bool (m ≤ n)
≤-Bool {n = n} zN Nn           = subst (λ t → Bool t) (sym (<-0S n)) tB
≤-Bool (sN Nm) zN              = subst (λ t → Bool t) (sym (S≰0 Nm)) fB
≤-Bool (sN {m} Nm) (sN {n} Nn) = subst (λ t → Bool t)
                                        (sym (≤-SS m n))
                                        (≤-Bool Nm Nn)
