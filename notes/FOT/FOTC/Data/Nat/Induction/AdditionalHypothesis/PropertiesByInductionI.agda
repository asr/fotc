------------------------------------------------------------------------------
-- Arithmetic properties: Testing the induction principle
------------------------------------------------------------------------------

module FOT.FOTC.Data.Nat.Induction.AdditionalHypothesis.PropertiesByInductionI
  where

open import FOTC.Base
open import FOTC.Data.Nat hiding ( N-ind )

------------------------------------------------------------------------------
-- Induction principle with the additional hypothesis.
N-ind₁ : (A : D → Set) →
         A zero →
         (∀ {n} → N n → A n → A (succ₁ n)) →
         ∀ {n} → N n → A n
N-ind₁ A A0 h nzero      = A0
N-ind₁ A A0 h (nsucc Nn) = h Nn (N-ind₁ A A0 h Nn)

-- Induction principle without the additional hypothesis.
N-ind₂ : (A : D → Set) →
        A zero →
        (∀ {n} → A n → A (succ₁ n)) →
        ∀ {n} → N n → A n
N-ind₂ A A0 h nzero      = A0
N-ind₂ A A0 h (nsucc Nn) = h (N-ind₂ A A0 h Nn)

------------------------------------------------------------------------------

pred-N₁ : ∀ {n} → N n → N (pred₁ n)
pred-N₁ = N-ind₁ A A0 is
  where
  A : D → Set
  A i = N (pred₁ i)

  A0 : A zero
  A0 = subst N (sym pred-0) nzero

  is : ∀ {i} → N i → A i → A (succ₁ i)
  is {i} Ni ih = subst N (sym (pred-S i)) Ni

-- It is not possible to prove pred-N using N-ind₂.
-- pred-N₂ : ∀ {n} → N n → N (pred₁ n)
-- pred-N₂ = N-ind₂ A A0 is
--   where
--   A : D → Set
--   A i = N (pred₁ i)

--   A0 : A zero
--   A0 = subst N (sym pred-0) nzero

--   -- We need the hypothesis N i.
--   is : ∀ {i} → A i → A (succ₁ i)
--   is {i} ih = subst N (sym (pred-S i)) {!!}

+-N₁ : ∀ {m n} → N m → N n → N (m + n)
+-N₁ {n = n} Nm Nn = N-ind₁ A A0 is Nm
  where
  A : D → Set
  A i = N (i + n)

  A0 : A zero
  A0 = subst N (sym (+-0x n)) Nn

  is : ∀ {i} → N i → A i → A (succ₁ i)
  is {i} _ ih = subst N (sym (+-Sx i n)) (nsucc ih)

+-N₂ : ∀ {m n} → N m → N n → N (m + n)
+-N₂ {n = n} Nm Nn = N-ind₂ A A0 is Nm
  where
  A : D → Set
  A i = N (i + n)

  A0 : A zero
  A0 = subst N (sym (+-0x n)) Nn

  is : ∀ {i} → A i → A (succ₁ i)
  is {i} ih = subst N (sym (+-Sx i n)) (nsucc ih)
