------------------------------------------------------------------------------
-- The Booleans properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Bool.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Basic properties

true&&x≡x : ∀ b → true && b ≡ b
true&&x≡x b = if-true b

false&&x≡false : ∀ b → false && b ≡ false
false&&x≡false b = if-false false

not-t : not true ≡ false
not-t = if-true false

not-f : not false ≡ true
not-f = if-false true

&&-Bool : ∀ {a b} → Bool a → Bool b → Bool (a && b)
&&-Bool {b = b} tB Bb = subst Bool (sym (true&&x≡x b )) Bb
&&-Bool {b = b} fB Bb = subst Bool (sym (false&&x≡false b)) fB

not-Bool : ∀ {b} → Bool b → Bool (not b)
not-Bool tB = subst Bool (sym not-t) fB
not-Bool fB = subst Bool (sym not-f) tB

&&-list₂-true : ∀ {a b} → Bool a → Bool b → a && b ≡ true →
                a ≡ true ∧ b ≡ true
&&-list₂-true tB tB h = refl , refl
&&-list₂-true tB fB h =
  ⊥-elim (true≢false (trans (sym h) (true&&x≡x false)))
&&-list₂-true fB tB h =
  ⊥-elim (true≢false (trans (sym h) (false&&x≡false true)))
&&-list₂-true fB fB h =
  ⊥-elim (true≢false (trans (sym h) (false&&x≡false false)))

&&-list₂-true₁ : ∀ {a b} → Bool a → Bool b → a && b ≡ true → a ≡ true
&&-list₂-true₁ Ba Bb h = ∧-proj₁ (&&-list₂-true Ba Bb h)

&&-list₂-true₂ : ∀ {a b} → Bool a → Bool b → a && b ≡ true → b ≡ true
&&-list₂-true₂ Ba Bb h = ∧-proj₂ (&&-list₂-true Ba Bb h)

&&-list₄-some-false : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
                     (a ≡ false ∨ b ≡ false ∨ c ≡ false ∨ d ≡ false) →
                     a && b && c && d ≡ false
&&-list₄-some-false tB Bb Bc Bd (inj₁ h) = ⊥-elim (true≢false h)
&&-list₄-some-false tB tB Bc Bd (inj₂ (inj₁ h)) = ⊥-elim (true≢false h)
&&-list₄-some-false tB tB tB Bd (inj₂ (inj₂ (inj₁ h))) = ⊥-elim (true≢false h)
&&-list₄-some-false tB tB tB tB (inj₂ (inj₂ (inj₂ h))) = ⊥-elim (true≢false h)
&&-list₄-some-false tB tB tB fB (inj₂ (inj₂ (inj₂ h))) =
  trans (true&&x≡x (true && true && false))
        (trans (true&&x≡x (true && false)) (true&&x≡x false))
&&-list₄-some-false tB tB fB tB (inj₂ (inj₂ (inj₁ h))) =
  trans (true&&x≡x (true && false && true))
        (trans (true&&x≡x (false && true)) (false&&x≡false true))
&&-list₄-some-false tB tB fB tB (inj₂ (inj₂ (inj₂ h))) = ⊥-elim (true≢false h)
&&-list₄-some-false tB tB fB fB (inj₂ (inj₂ h)) =
  trans (true&&x≡x (true && false && false))
        (trans (true&&x≡x (false && false)) (false&&x≡false false))
&&-list₄-some-false {c = c} {d} tB fB Bc Bd (inj₂ h) =
  trans (true&&x≡x (false && c && d))
        (false&&x≡false (c && d))
&&-list₄-some-false {b = b} {c} {d} fB Bb Bc Bd _ =
  false&&x≡false (b && c && d)

&&-list₄-true : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
                a && b && c && d ≡ true →
                a ≡ true ∧ b ≡ true ∧ c ≡ true ∧ d ≡ true
&&-list₄-true tB tB tB tB h = refl , refl , refl , refl
&&-list₄-true tB tB tB fB h =
  ⊥-elim (true≢false
           (trans (sym h)
                  (&&-list₄-some-false tB tB tB fB (inj₂ (inj₂ (inj₂ refl))))))
&&-list₄-true tB tB fB Bd h =
  ⊥-elim (true≢false
           (trans (sym h)
                  (&&-list₄-some-false tB tB fB Bd (inj₂ (inj₂ (inj₁ refl))))))
&&-list₄-true tB fB Bc Bd h =
  ⊥-elim (true≢false
          (trans (sym h)
                 (&&-list₄-some-false tB fB Bc Bd (inj₂ (inj₁ refl)))))
&&-list₄-true fB Bb Bc Bd h =
  ⊥-elim (true≢false (trans (sym h)
                            (&&-list₄-some-false fB Bb Bc Bd (inj₁ refl))))

&&-list₄-true₁ : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
                 a && b && c && d ≡ true → a ≡ true
&&-list₄-true₁ Ba Bb Bc Bd h = ∧-proj₁ (&&-list₄-true Ba Bb Bc Bd h)

&&-list₄-true₂ : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
                 a && b && c && d ≡ true → b ≡ true
&&-list₄-true₂ Ba Bb Bc Bd h = ∧-proj₁ (∧-proj₂ (&&-list₄-true Ba Bb Bc Bd h))

&&-list₄-true₃ : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
                 a && b && c && d ≡ true → c ≡ true
&&-list₄-true₃ Ba Bb Bc Bd h =
  ∧-proj₁ (∧-proj₂ (∧-proj₂ (&&-list₄-true Ba Bb Bc Bd h)))

&&-list₄-true₄ : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
                 a && b && c && d ≡ true → d ≡ true
&&-list₄-true₄ Ba Bb Bc Bd h =
  ∧-proj₂ (∧-proj₂ (∧-proj₂ (&&-list₄-true Ba Bb Bc Bd h)))

x≢not-x : ∀ {b} → Bool b → b ≢ not b
x≢not-x tB h = true≢false (trans h not-t)
x≢not-x fB h = true≢false (sym (trans h not-f))

not-x≢x : ∀ {b} → Bool b → not b ≢ b
not-x≢x Bb h = x≢not-x Bb (sym h)

not-involutive : ∀ {b} → Bool b → not (not b) ≡ b
not-involutive tB = trans (cong not not-t) not-f
not-involutive fB = trans (cong not not-f) not-t

------------------------------------------------------------------------------
-- Properties with inequalities

<-Bool : ∀ {m n} → N m → N n → Bool (m < n)
<-Bool zN          zN          = subst Bool (sym <-00) fB
<-Bool zN          (sN {n} Nn) = subst Bool (sym (<-0S n)) tB
<-Bool (sN {m} Nm) zN          = subst Bool (sym (<-S0 m)) fB
<-Bool (sN {m} Nm) (sN {n} Nn) = subst Bool (sym (<-SS m n)) (<-Bool Nm Nn)

≤-Bool : ∀ {m n} → N m → N n → Bool (m ≤ n)
≤-Bool {n = n} zN          Nn          = subst Bool (sym (<-0S n)) tB
≤-Bool         (sN Nm)     zN          = subst Bool (sym (Sx≰0 Nm)) fB
≤-Bool         (sN {m} Nm) (sN {n} Nn) =
  subst Bool (sym (<-SS m (succ₁ n))) (≤-Bool Nm Nn)
