------------------------------------------------------------------------------
-- The Booleans properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Bool.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Bool
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Basic properties

postulate t&&x≡x : ∀ b → true && b ≡ b
{-# ATP prove t&&x≡x #-}

postulate f&&x≡f : ∀ b → false && b ≡ false
{-# ATP prove f&&x≡f #-}

&&-Bool : ∀ {a b} → Bool a → Bool b → Bool (a && b)
&&-Bool {b = b} tB Bb = prf
  where postulate prf : Bool (true && b)
        {-# ATP prove prf #-}
&&-Bool {b = b} fB Bb = prf
  where postulate prf : Bool (false && b)
        {-# ATP prove prf #-}

not-Bool : ∀ {b} → Bool b → Bool (not b)
not-Bool tB = prf
  where postulate prf : Bool (not true)
        {-# ATP prove prf #-}
not-Bool fB = prf
  where postulate prf : Bool (not false)
        {-# ATP prove prf #-}

&&-list₂-t : ∀ {a b} → Bool a → Bool b → a && b ≡ true → a ≡ true ∧ b ≡ true
&&-list₂-t tB tB h = refl , refl
&&-list₂-t tB fB h = ⊥-elim (true≢false (trans (sym h) (t&&x≡x false)))
&&-list₂-t fB tB h = ⊥-elim (true≢false (trans (sym h) (f&&x≡f true)))
&&-list₂-t fB fB h = ⊥-elim (true≢false (trans (sym h) (f&&x≡f false)))

&&-list₂-t₁ : ∀ {a b} → Bool a → Bool b → a && b ≡ true → a ≡ true
&&-list₂-t₁ Ba Bb h = ∧-proj₁ (&&-list₂-t Ba Bb h)

&&-list₂-t₂ : ∀ {a b} → Bool a → Bool b → a && b ≡ true → b ≡ true
&&-list₂-t₂ Ba Bb h = ∧-proj₂ (&&-list₂-t Ba Bb h)

&&-list₄-some-f : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
                  (a ≡ false ∨ b ≡ false ∨ c ≡ false ∨ d ≡ false) →
                  a && b && c && d ≡ false
&&-list₄-some-f tB Bb Bc Bd (inj₁ h) = ⊥-elim (true≢false h)
&&-list₄-some-f tB tB Bc Bd (inj₂ (inj₁ h)) = ⊥-elim (true≢false h)
&&-list₄-some-f tB tB tB Bd (inj₂ (inj₂ (inj₁ h))) = ⊥-elim (true≢false h)
&&-list₄-some-f tB tB tB tB (inj₂ (inj₂ (inj₂ h))) = ⊥-elim (true≢false h)
&&-list₄-some-f tB tB tB fB (inj₂ (inj₂ (inj₂ h))) =
  trans (t&&x≡x (true && true && false))
        (trans (t&&x≡x (true && false)) (t&&x≡x false))
&&-list₄-some-f tB tB fB tB (inj₂ (inj₂ (inj₁ h))) =
  trans (t&&x≡x (true && false && true))
        (trans (t&&x≡x (false && true)) (f&&x≡f true))
&&-list₄-some-f tB tB fB tB (inj₂ (inj₂ (inj₂ h))) = ⊥-elim (true≢false h)
&&-list₄-some-f tB tB fB fB (inj₂ (inj₂ h)) =
  trans (t&&x≡x (true && false && false))
        (trans (t&&x≡x (false && false)) (f&&x≡f false))
&&-list₄-some-f {c = c} {d} tB fB Bc Bd (inj₂ h) =
  trans (t&&x≡x (false && c && d)) (f&&x≡f (c && d))
&&-list₄-some-f {b = b} {c} {d} fB Bb Bc Bd _ = f&&x≡f (b && c && d)

&&-list₄-t : ∀ {a b c d} → Bool a → Bool b → Bool c → Bool d →
             a && b && c && d ≡ true →
             a ≡ true ∧ b ≡ true ∧ c ≡ true ∧ d ≡ true
&&-list₄-t tB tB tB tB h = refl , refl , refl , refl
&&-list₄-t tB tB tB fB h =
  ⊥-elim (true≢false
           (trans (sym h)
                  (&&-list₄-some-f tB tB tB fB (inj₂ (inj₂ (inj₂ refl))))))
&&-list₄-t tB tB fB Bd h =
  ⊥-elim (true≢false
           (trans (sym h)
                  (&&-list₄-some-f tB tB fB Bd (inj₂ (inj₂ (inj₁ refl))))))
&&-list₄-t tB fB Bc Bd h =
  ⊥-elim (true≢false
           (trans (sym h) (&&-list₄-some-f tB fB Bc Bd (inj₂ (inj₁ refl)))))
&&-list₄-t fB Bb Bc Bd h =
  ⊥-elim (true≢false (trans (sym h) (&&-list₄-some-f fB Bb Bc Bd (inj₁ refl))))

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
x≢not-x tB = prf
  where postulate prf : true ≡ not true → ⊥
        {-# ATP prove prf #-}
x≢not-x fB = prf
  where postulate prf : false ≡ not false → ⊥
        {-# ATP prove prf #-}

not-x≢x : ∀ {b} → Bool b → not b ≢ b
not-x≢x Bb h = x≢not-x Bb (sym h)

not-involutive : ∀ {b} → Bool b → not (not b) ≡ b
not-involutive tB = prf
  where postulate prf : not (not true) ≡ true
        {-# ATP prove prf #-}
not-involutive fB = prf
  where postulate prf : not (not false) ≡ false
        {-# ATP prove prf #-}

------------------------------------------------------------------------------
-- Properties with inequalities

<-Bool : ∀ {m n} → N m → N n → Bool (m < n)
<-Bool zN zN = prf
  where postulate prf : Bool (zero < zero)
        {-# ATP prove prf #-}
<-Bool zN (sN {n} Nn) = prf
  where postulate prf : Bool (zero < succ₁ n)
        {-# ATP prove prf #-}
<-Bool (sN {m} Nm) zN = prf
  where postulate prf : Bool (succ₁ m < zero)
        {-# ATP prove prf #-}
<-Bool (sN {m} Nm) (sN {n} Nn) = prf (<-Bool Nm Nn)
  where postulate prf : Bool (m < n) → Bool (succ₁ m < succ₁ n)
        {-# ATP prove prf #-}

≤-Bool : ∀ {m n} → N m → N n → Bool (m ≤ n)
≤-Bool {n = n} zN Nn = prf
  where postulate prf : Bool (zero ≤ n)
        {-# ATP prove prf #-}
≤-Bool (sN {m} Nm) zN = prf
  where postulate prf : Bool (succ₁ m ≤ zero)
        {-# ATP prove prf Sx≰0 #-}
≤-Bool (sN {m} Nm) (sN {n} Nn) = prf (≤-Bool Nm Nn)
  where postulate prf : Bool (m ≤ n) → Bool (succ₁ m ≤ succ₁ n)
        {-# ATP prove prf #-}
