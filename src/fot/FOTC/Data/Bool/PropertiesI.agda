------------------------------------------------------------------------------
-- The Booleans properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Bool.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Congruence properties

&&-leftCong : ∀ {a b c} → a ≡ b → a && c ≡ b && c
&&-leftCong refl = refl

&&-rightCong : ∀ {a b c} → b ≡ c → a && b ≡ a && c
&&-rightCong refl = refl

&&-cong : ∀ {a b c d } → a ≡ c → b ≡ d → a && b ≡ c && d
&&-cong refl refl = refl

notCong : ∀ {a b} → a ≡ b → not a ≡ not b
notCong refl = refl

------------------------------------------------------------------------------
-- Basic properties

t&&x≡x : ∀ b → true && b ≡ b
t&&x≡x b = if-true b

f&&x≡f : ∀ b → false && b ≡ false
f&&x≡f b = if-false false

not-t : not true ≡ false
not-t = if-true false

not-f : not false ≡ true
not-f = if-false true

&&-Bool : ∀ {a b} → Bool a → Bool b → Bool (a && b)
&&-Bool {b = b} btrue  Bb = subst Bool (sym (t&&x≡x b)) Bb
&&-Bool {b = b} bfalse Bb = subst Bool (sym (f&&x≡f b)) bfalse

not-Bool : ∀ {b} → Bool b → Bool (not b)
not-Bool btrue  = subst Bool (sym not-t) bfalse
not-Bool bfalse = subst Bool (sym not-f) btrue

&&-comm : ∀ {a b} → Bool a → Bool b → a && b ≡ b && a
&&-comm btrue  btrue  = refl
&&-comm btrue  bfalse = trans (t&&x≡x false) (sym (f&&x≡f true))
&&-comm bfalse btrue  = trans (f&&x≡f true) (sym (t&&x≡x false))
&&-comm bfalse bfalse = refl

&&-assoc : ∀ {a b c} → Bool a → Bool b → Bool c → (a && b) && c ≡ a && b && c
&&-assoc btrue btrue btrue = &&-cong (t&&x≡x true) (sym (t&&x≡x true))
&&-assoc btrue btrue bfalse = &&-cong (t&&x≡x true) (sym (t&&x≡x false))
&&-assoc btrue bfalse btrue =
  (true && false) && true ≡⟨ &&-comm (&&-Bool btrue bfalse) btrue ⟩
  true && (true && false) ≡⟨ t&&x≡x (true && false) ⟩
  true && false           ≡⟨ &&-rightCong (sym (f&&x≡f true)) ⟩
  true && false && true   ∎
&&-assoc btrue bfalse bfalse =
  (true && false) && false ≡⟨ &&-comm (&&-Bool btrue bfalse) bfalse ⟩
  false && (true && false) ≡⟨ f&&x≡f (true && false) ⟩
  false                    ≡⟨ sym (f&&x≡f false) ⟩
  false && false           ≡⟨ sym (t&&x≡x (false && false)) ⟩
  true && false && false   ∎
&&-assoc bfalse btrue btrue = &&-cong (f&&x≡f true) (sym (t&&x≡x true))
&&-assoc bfalse btrue bfalse = &&-cong (f&&x≡f true) (sym (t&&x≡x false))
&&-assoc bfalse bfalse btrue =
  (false && false) && true ≡⟨ &&-comm (&&-Bool bfalse bfalse) btrue ⟩
  true && (false && false) ≡⟨ t&&x≡x (false && false) ⟩
  false && false           ≡⟨ f&&x≡f false ⟩
  false                    ≡⟨ sym (f&&x≡f (false && true)) ⟩
  false && false && true   ∎
&&-assoc bfalse bfalse bfalse = &&-cong (f&&x≡f false) (sym (f&&x≡f false))

&&-list₂-t : ∀ {a b} → Bool a → Bool b → a && b ≡ true → a ≡ true ∧ b ≡ true
&&-list₂-t btrue  btrue  h = refl , refl
&&-list₂-t btrue  bfalse h = ⊥-elim (t≢f (trans (sym h) (t&&x≡x false)))
&&-list₂-t bfalse btrue  h = ⊥-elim (t≢f (trans (sym h) (f&&x≡f true)))
&&-list₂-t bfalse bfalse h = ⊥-elim (t≢f (trans (sym h) (f&&x≡f false)))

&&-list₂-t₁ : ∀ {a b} → Bool a → Bool b → a && b ≡ true → a ≡ true
&&-list₂-t₁ Ba Bb h = ∧-proj₁ (&&-list₂-t Ba Bb h)

&&-list₂-t₂ : ∀ {a b} → Bool a → Bool b → a && b ≡ true → b ≡ true
&&-list₂-t₂ Ba Bb h = ∧-proj₂ (&&-list₂-t Ba Bb h)

&&-list₂-all-t : ∀ {a b} → Bool a → Bool b →
                 (a ≡ true ∧ b ≡ true) →
                 a && b ≡ true
&&-list₂-all-t btrue  btrue  h         = t&&x≡x true
&&-list₂-all-t btrue  bfalse (h₁ , h₂) = ⊥-elim (t≢f (sym h₂))
&&-list₂-all-t bfalse Bb     (h₁ , h₂) = ⊥-elim (t≢f (sym h₁))

&&-list₃-all-t : ∀ {a b c} → Bool a → Bool b → Bool c →
                 a ≡ true ∧ b ≡ true ∧ c ≡ true →
                 a && b && c ≡ true
&&-list₃-all-t btrue btrue btrue h = trans (t&&x≡x (true && true)) (t&&x≡x true)
&&-list₃-all-t btrue btrue bfalse (h₁ , h₂ , h₃) = ⊥-elim (t≢f (sym h₃))
&&-list₃-all-t btrue bfalse Bc (h₁ , h₂ , h₃) = ⊥-elim (t≢f (sym h₂))
&&-list₃-all-t bfalse Bb Bc (h₁ , h₂ , h₃) = ⊥-elim (t≢f (sym h₁))

&&-list₄-all-t : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
                 a ≡ true ∧ b ≡ true ∧ c ≡ true ∧ d ≡ true →
                 a && b && c && d ≡ true
&&-list₄-all-t btrue btrue btrue btrue h =
  trans₂ (t&&x≡x (true && true && true)) (t&&x≡x (true && true)) (t&&x≡x true)
&&-list₄-all-t btrue btrue btrue bfalse (h₁ , h₂ , h₃ , h₄) = ⊥-elim (t≢f (sym h₄))
&&-list₄-all-t btrue btrue bfalse Bd (h₁ , h₂ , h₃ , h₄) = ⊥-elim (t≢f (sym h₃))
&&-list₄-all-t btrue bfalse Bc Bd (h₁ , h₂ , h₃ , h₄) = ⊥-elim (t≢f (sym h₂))
&&-list₄-all-t bfalse Bb Bc Bd (h₁ , h₂ , h₃ , h₄) = ⊥-elim (t≢f (sym h₁))

&&-list₄-some-f : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
                  a ≡ false ∨ b ≡ false ∨ c ≡ false ∨ d ≡ false →
                  a && b && c && d ≡ false
&&-list₄-some-f btrue Bb Bc Bd (inj₁ h) = ⊥-elim (t≢f h)
&&-list₄-some-f btrue btrue Bc Bd (inj₂ (inj₁ h)) = ⊥-elim (t≢f h)
&&-list₄-some-f btrue btrue btrue Bd (inj₂ (inj₂ (inj₁ h))) = ⊥-elim (t≢f h)
&&-list₄-some-f btrue btrue btrue btrue (inj₂ (inj₂ (inj₂ h))) = ⊥-elim (t≢f h)
&&-list₄-some-f btrue btrue btrue bfalse (inj₂ (inj₂ (inj₂ h))) =
  trans (t&&x≡x (true && true && false))
        (trans (t&&x≡x (true && false)) (t&&x≡x false))
&&-list₄-some-f btrue btrue bfalse btrue (inj₂ (inj₂ (inj₁ h))) =
  trans (t&&x≡x (true && false && true))
        (trans (t&&x≡x (false && true)) (f&&x≡f true))
&&-list₄-some-f btrue btrue bfalse btrue (inj₂ (inj₂ (inj₂ h))) = ⊥-elim (t≢f h)
&&-list₄-some-f btrue btrue bfalse bfalse (inj₂ (inj₂ h)) =
  trans (t&&x≡x (true && false && false))
        (trans (t&&x≡x (false && false)) (f&&x≡f false))
&&-list₄-some-f {c = c} {d} btrue bfalse Bc Bd (inj₂ h) =
  trans (t&&x≡x (false && c && d)) (f&&x≡f (c && d))
&&-list₄-some-f {b = b} {c} {d} bfalse Bb Bc Bd _ = f&&x≡f (b && c && d)

&&-list₄-t : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
             a && b && c && d ≡ true →
             a ≡ true ∧ b ≡ true ∧ c ≡ true ∧ d ≡ true
&&-list₄-t btrue btrue btrue btrue h = refl , refl , refl , refl
&&-list₄-t btrue btrue btrue bfalse h =
  ⊥-elim (t≢f
           (trans (sym h)
                  (&&-list₄-some-f btrue btrue btrue bfalse (inj₂ (inj₂ (inj₂ refl))))))
&&-list₄-t btrue btrue bfalse Bd h =
  ⊥-elim (t≢f
           (trans (sym h)
                  (&&-list₄-some-f btrue btrue bfalse Bd (inj₂ (inj₂ (inj₁ refl))))))
&&-list₄-t btrue bfalse Bc Bd h =
  ⊥-elim (t≢f
           (trans (sym h) (&&-list₄-some-f btrue bfalse Bc Bd (inj₂ (inj₁ refl)))))
&&-list₄-t bfalse Bb Bc Bd h =
  ⊥-elim (t≢f (trans (sym h) (&&-list₄-some-f bfalse Bb Bc Bd (inj₁ refl))))

&&-list₄-t₁ : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
              a && b && c && d ≡ true → a ≡ true
&&-list₄-t₁ Ba Bb Bc Bd h = ∧-proj₁ (&&-list₄-t Ba Bb Bc Bd h)

&&-list₄-t₂ : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
              a && b && c && d ≡ true → b ≡ true
&&-list₄-t₂ Ba Bb Bc Bd h = ∧-proj₁ (∧-proj₂ (&&-list₄-t Ba Bb Bc Bd h))

&&-list₄-t₃ : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
              a && b && c && d ≡ true → c ≡ true
&&-list₄-t₃ Ba Bb Bc Bd h =
  ∧-proj₁ (∧-proj₂ (∧-proj₂ (&&-list₄-t Ba Bb Bc Bd h)))

&&-list₄-t₄ : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
              a && b && c && d ≡ true → d ≡ true
&&-list₄-t₄ Ba Bb Bc Bd h =
  ∧-proj₂ (∧-proj₂ (∧-proj₂ (&&-list₄-t Ba Bb Bc Bd h)))

x≢not-x : ∀ {b} → Bool b → b ≢ not b
x≢not-x btrue  h = t≢f (trans h not-t)
x≢not-x bfalse h = t≢f (sym (trans h not-f))

not-x≢x : ∀ {b} → Bool b → not b ≢ b
not-x≢x Bb h = x≢not-x Bb (sym h)

not-involutive : ∀ {b} → Bool b → not (not b) ≡ b
not-involutive btrue  = trans (notCong not-t) not-f
not-involutive bfalse = trans (notCong not-f) not-t

------------------------------------------------------------------------------
-- Properties with inequalities

lt-Bool : ∀ {m n} → N m → N n → Bool (lt m n)
lt-Bool nzero          nzero          = subst Bool (sym lt-00) bfalse
lt-Bool nzero          (nsucc {n} Nn) = subst Bool (sym (lt-0S n)) btrue
lt-Bool (nsucc {m} Nm) nzero          = subst Bool (sym (lt-S0 m)) bfalse
lt-Bool (nsucc {m} Nm) (nsucc {n} Nn) = subst Bool (sym (lt-SS m n)) (lt-Bool Nm Nn)

le-Bool : ∀ {m n} → N m → N n → Bool (le m n)
le-Bool {n = n} nzero          Nn             = subst Bool (sym (lt-0S n)) btrue
le-Bool         (nsucc Nm)     nzero          = subst Bool (sym (Sx≰0 Nm)) bfalse
le-Bool         (nsucc {m} Nm) (nsucc {n} Nn) =
  subst Bool (sym (lt-SS m (succ₁ n))) (le-Bool Nm Nn)
