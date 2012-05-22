------------------------------------------------------------------------------
-- The Booleans properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Bool.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning
open import Common.Function

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.Type


------------------------------------------------------------------------------
-- Basic properties

&&-Bool : ∀ {b₁ b₂} → Bool b₁ → Bool b₂ → Bool (b₁ && b₂)
&&-Bool tB tB = subst Bool (sym &&-tt) tB
&&-Bool tB fB = subst Bool (sym &&-tf) fB
&&-Bool fB tB = subst Bool (sym &&-ft) fB
&&-Bool fB fB = subst Bool (sym &&-ff) fB

not-Bool : ∀ {b} → Bool b → Bool (not b)
not-Bool tB = subst Bool (sym not-t) fB
not-Bool fB = subst Bool (sym not-f) tB

&&-comm : ∀ {b₁ b₂} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ b₂ && b₁
&&-comm tB tB = refl
&&-comm tB fB = trans &&-tf (sym &&-ft)
&&-comm fB tB = trans &&-ft (sym &&-tf)
&&-comm fB fB = refl

x&&false≡false : ∀ {b} → Bool b → b && false ≡ false
x&&false≡false tB = &&-tf
x&&false≡false fB = &&-ff

false&&x≡false : ∀ {b} → Bool b → false && b ≡ false
false&&x≡false tB = &&-ft
false&&x≡false fB = &&-ff

true&&x≡x : ∀ {b} → Bool b → true && b ≡ b
true&&x≡x tB = &&-tt
true&&x≡x fB = &&-tf

-- See the ATP version.
postulate
  &&-assoc : ∀ {b₁ b₂ b₃} → Bool b₁ → Bool b₂ → Bool b₃ →
             (b₁ && b₂) && b₃ ≡ b₁ && b₂ && b₃

&&-true₃ : true && true && true ≡ true
&&-true₃ =
  true && true && true
    ≡⟨ subst (λ t → true && true && true ≡ true && t) &&-tt refl ⟩
  true && true
    ≡⟨ &&-tt ⟩
  true ∎

&&-true₄ : true && true && true && true ≡ true
&&-true₄ =
  true && true && true && true
    ≡⟨ subst (λ t → true && true && true && true ≡ true && t) &&-true₃ refl ⟩
  true && true
    ≡⟨ &&-tt ⟩
  true ∎

&&-proj₁ : ∀ {b₁ b₂} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ true → b₁ ≡ true
&&-proj₁ tB _ _    = refl
&&-proj₁ fB tB h = ⊥-elim $ true≢false $ trans (sym h) &&-ft
&&-proj₁ fB fB h = ⊥-elim $ true≢false $ trans (sym h) &&-ff

&&-proj₂ : ∀ {b₁ b₂} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ true → b₂ ≡ true
&&-proj₂ _  tB _   = refl
&&-proj₂ tB fB h = ⊥-elim $ true≢false $ trans (sym h) &&-tf
&&-proj₂ fB fB h = ⊥-elim $ true≢false $ trans (sym h) &&-ff

&&₃-proj₁ : ∀ {b₁ b₂ b₃ b₄} →
            Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
            b₁ && b₂ && b₃ && b₄ ≡ true →
            b₁ ≡ true
&&₃-proj₁ tB _ _ _ _ = refl
&&₃-proj₁ {b₂ = b₂} {b₃} {b₄} fB Bb₂ Bb₃ Bb₄ h =
  ⊥-elim $ true≢false $ trans (sym h) prf
  where
  prf : false && b₂ && b₃ && b₄ ≡ false
  prf = false&&x≡false (&&-Bool Bb₂ (&&-Bool Bb₃ Bb₄))

&&₃-proj₂ : ∀ {b₁ b₂ b₃ b₄} →
            Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
            b₁ && b₂ && b₃ && b₄ ≡ true →
            b₂ ≡ true
&&₃-proj₂ _ tB _ _ _ = refl
&&₃-proj₂ {b₁} {b₃ = b₃} {b₄} Bb₁ fB Bb₃ Bb₄ h =
  ⊥-elim $ true≢false $ trans (sym h) prf
  where
  prf : b₁ && false && b₃ && b₄ ≡ false
  prf =
    b₁ && false && b₃ && b₄
       ≡⟨ subst (λ t → b₁ && false && b₃ && b₄ ≡ b₁ && t)
                (false&&x≡false (&&-Bool Bb₃ Bb₄))
                refl
       ⟩
    b₁ && false
       ≡⟨ x&&false≡false Bb₁ ⟩
    false ∎

&&₃-proj₃ : ∀ {b₁ b₂ b₃ b₄} →
            Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
            b₁ && b₂ && b₃ && b₄ ≡ true →
            b₃ ≡ true
&&₃-proj₃ _ _ tB _ _ = refl
&&₃-proj₃ {b₁} {b₂} {b₄ = b₄} Bb₁ Bb₂ fB Bb₄ h =
  ⊥-elim $ true≢false $ trans (sym h) prf
  where
  prf : b₁ && b₂ && false && b₄ ≡ false
  prf =
    b₁ && b₂ && false && b₄
       ≡⟨ subst (λ t → b₁ && b₂ && false && b₄ ≡ b₁ && b₂ && t)
                (false&&x≡false Bb₄)
                refl
       ⟩
    b₁ && b₂ && false
       ≡⟨ subst (λ t → b₁ && b₂ && false ≡ b₁ && t) (x&&false≡false Bb₂) refl ⟩
    b₁ && false
       ≡⟨ x&&false≡false Bb₁ ⟩
    false ∎

&&₃-proj₄ : ∀ {b₁ b₂ b₃ b₄} →
            Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
            b₁ && b₂ && b₃ && b₄ ≡ true →
            b₄ ≡ true
&&₃-proj₄ _ _ _ tB _ = refl
&&₃-proj₄ {b₁} {b₂} {b₃} Bb₁ Bb₂ Bb₃ fB h =
  ⊥-elim $ true≢false $ trans (sym h) prf
  where
  prf : b₁ && b₂ && b₃ && false ≡ false
  prf =
    b₁ && b₂ && b₃ && false
       ≡⟨ subst (λ t → b₁ && b₂ && b₃ && false ≡ b₁ && b₂ && t)
                (x&&false≡false Bb₃)
                refl
       ⟩
    b₁ && b₂ && false
       ≡⟨ subst (λ t → b₁ && b₂ && false ≡ b₁ && t) (x&&false≡false Bb₂) refl ⟩
    b₁ && false
       ≡⟨ x&&false≡false Bb₁ ⟩
    false ∎

x≢not-x : ∀ {b} → Bool b → b ≢ not b
x≢not-x tB h = true≢false (trans h not-t)
x≢not-x fB h = true≢false (sym (trans h not-f))

not-x≢x : ∀ {b} → Bool b → not b ≢ b
not-x≢x Bb h = x≢not-x Bb (sym h)

not² : ∀ {b} → Bool b → not (not b) ≡ b
not² tB = trans (cong not not-t) not-f
not² fB = trans (cong not not-f) not-t

------------------------------------------------------------------------------
-- Properties with inequalities

≤-Bool : ∀ {m n} → N m → N n → Bool (m ≤ n)
≤-Bool {n = n} zN Nn           = subst Bool (sym $ <-0S n) tB
≤-Bool (sN Nm) zN              = subst Bool (sym $ Sx≰0 Nm) fB
≤-Bool (sN {m} Nm) (sN {n} Nn) = subst Bool
                                       (sym $ <-SS m (succ₁ n))
                                       (≤-Bool Nm Nn)
