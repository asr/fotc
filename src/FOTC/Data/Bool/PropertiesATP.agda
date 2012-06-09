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

postulate true&&x≡x : ∀ b → true && b ≡ b
{-# ATP prove true&&x≡x #-}

postulate false&&x≡false : ∀ b → false && b ≡ false
{-# ATP prove false&&x≡false #-}

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
