------------------------------------------------------------------------------
-- Testing some inductive predicates for inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.Inequalities.InductivePredicates where

open import FOTC.Base
open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

module m₁ where
  data _≤_ : D → D → Set where
    z≤n : ∀ n → zero ≤ n
    s≤s : ∀ {m n} → m ≤ n → succ₁ m ≤ succ₁ n

  _<_ : D → D → Set
  m < n = succ₁ m ≤ n

  _≥_ : D → D → Set
  m ≥ n = n ≤ m

  _>_ : D → D → Set
  m > n = n < m

  x≤y→x≤Sy : ∀ {m n} → m ≤ n → m ≤ succ₁ n
  x≤y→x≤Sy {.zero} {n} (z≤n .n)  = z≤n (succ₁ n)
  x≤y→x≤Sy             (s≤s m≤n) = s≤s (x≤y→x≤Sy m≤n)

module m₂ where
  data _≤_ : D → D → Set where
    z≤n : ∀ {n} → N n → zero ≤ n
    s≤s : ∀ {m n} → N m → N n → m ≤ n → succ₁ m ≤ succ₁ n

  _<_ : D → D → Set
  m < n = succ₁ m ≤ n

  _≥_ : D → D → Set
  m ≥ n = n ≤ m

  _>_ : D → D → Set
  m > n = n < m

  x≤y→x≤Sy : ∀ {m n} → m ≤ n → m ≤ succ₁ n
  x≤y→x≤Sy (z≤n Nn)        = z≤n (nsucc Nn)
  x≤y→x≤Sy (s≤s Nm Nn m≤n) = s≤s Nm (nsucc Nn) (x≤y→x≤Sy m≤n)

  postulate
    lt    : D → D → D
    lt-00 : lt zero zero                   ≡ false
    lt-0S : ∀ n → lt zero (succ₁ n)        ≡ true
    lt-S0 : ∀ n → lt (succ₁ n) zero        ≡ false
    lt-SS : ∀ m n → lt (succ₁ m) (succ₁ n) ≡ lt m n

  le : D → D → D
  le m n = lt m (succ₁ n)

  ≤→le : ∀ {m n} → m ≤ n → le m n ≡ true
  ≤→le {n = n} (z≤n Nn) = lt-0S n
  ≤→le (s≤s nzero nzero h) = trans (lt-SS zero [1]) (≤→le h)
  ≤→le (s≤s nzero (nsucc {n} Nn) h) = trans (lt-SS zero (succ₁ (succ₁ n))) (≤→le h)
  ≤→le (s≤s (nsucc {m} Nm) nzero h) = trans (lt-SS (succ₁ m) [1]) (≤→le h)
  ≤→le (s≤s (nsucc {m} Nm) (nsucc {n} Nn) h) =
    trans (lt-SS (succ₁ m) (succ₁ (succ₁ n))) (≤→le h)

  le→≤ : ∀ {m n} → N m → N n → le m n ≡ true → m ≤ n
  le→≤ nzero Nn h = z≤n Nn
  le→≤ (nsucc nzero) nzero h =
    ⊥-elim (true≢false (trans (sym h) (trans (lt-SS zero zero) lt-00)))
  le→≤ (nsucc (nsucc {m} Nm)) nzero h =
    ⊥-elim (true≢false (trans (sym h) (trans (lt-SS (succ₁ m) zero) (lt-S0 m))))
  le→≤ (nsucc {m} Nm) (nsucc {n} Nn) h =
    s≤s Nm Nn (le→≤ Nm Nn (trans (sym (lt-SS m (succ₁ n))) h))

module m₃ where
  data _≤_ : ∀ {m n} → N m → N n → Set where
    z≤n : ∀ {n} → (Nn : N n)                          → nzero ≤ Nn
    s≤s : ∀ {m n} → (Nm : N m) → (Nn : N n) → Nm ≤ Nn → nsucc Nm ≤ nsucc Nn

  _<_ : ∀ {m n} → N m → N n → Set
  Nm < Nn = nsucc Nm ≤ Nn

  _≥_ : ∀ {m n} → N m → N n → Set
  Nm ≥ Nn = Nn ≤ Nm

  _>_ : ∀ {m n} → N m → N n → Set
  Nm > Nn = Nn < Nm

  x≤y→x≤Sy : ∀ {m n} → (Nm : N m) → (Nn : N n) → Nm ≤ Nn → Nm ≤ nsucc Nn
  x≤y→x≤Sy .nzero       Nn         (z≤n .Nn)         = z≤n (nsucc Nn)
  x≤y→x≤Sy .(nsucc Nm) .(nsucc Nn) (s≤s Nm Nn Nm≤Nn) =
    s≤s Nm (nsucc Nn) (x≤y→x≤Sy Nm Nn Nm≤Nn)
