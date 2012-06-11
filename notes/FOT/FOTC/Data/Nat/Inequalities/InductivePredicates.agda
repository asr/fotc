------------------------------------------------------------------------------
-- Testing some inductive predicates for inequalities
------------------------------------------------------------------------------

-- Tested with FOT on 11 June 2012.

module FOT.FOTC.Data.Nat.Inequalities.InductivePredicates where

open import FOTC.Base
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------

module m₁ where
  data _≤_ : D → D → Set where
    z≤n : ∀ n             → zero   ≤ n
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
    z≤n : ∀ {n} → N n                 → zero   ≤ n
    s≤s : ∀ {m n} → N m → N n → m ≤ n → succ₁ m ≤ succ₁ n

  _<_ : D → D → Set
  m < n = succ₁ m ≤ n

  _≥_ : D → D → Set
  m ≥ n = n ≤ m

  _>_ : D → D → Set
  m > n = n < m

  x≤y→x≤Sy : ∀ {m n} → m ≤ n → m ≤ succ₁ n
  x≤y→x≤Sy (z≤n Nn)        = z≤n (sN Nn)
  x≤y→x≤Sy (s≤s Nm Nn m≤n) = s≤s Nm (sN Nn) (x≤y→x≤Sy m≤n)

module m₃ where
  data _≤_ : ∀ {m n} → N m → N n → Set where
    z≤n : ∀ {n} → (Nn : N n)                          → zN ≤ Nn
    s≤s : ∀ {m n} → (Nm : N m) → (Nn : N n) → Nm ≤ Nn → sN Nm ≤ sN Nn

  _<_ : ∀ {m n} → N m → N n → Set
  Nm < Nn = sN Nm ≤ Nn

  _≥_ : ∀ {m n} → N m → N n → Set
  Nm ≥ Nn = Nn ≤ Nm

  _>_ : ∀ {m n} → N m → N n → Set
  Nm > Nn = Nn < Nm

  x≤y→x≤Sy : ∀ {m n} → (Nm : N m) → (Nn : N n) → Nm ≤ Nn → Nm ≤ sN Nn
  x≤y→x≤Sy .zN       Nn      (z≤n .Nn)         = z≤n (sN Nn)
  x≤y→x≤Sy .(sN Nm) .(sN Nn) (s≤s Nm Nn Nm≤Nn) = s≤s Nm (sN Nn) (x≤y→x≤Sy Nm Nn Nm≤Nn)
