------------------------------------------------------------------------------
-- Definition of mutual inductive predicates
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}

module FOTC.MutualInductivePredicates where

open import FOTC.Base

------------------------------------------------------------------------------
-- Using mutual inductive predicates

data Even : D → Set
data Odd  : D → Set

data Even where
  ezero : Even zero
  esucc : ∀ {n} → Odd n → Even (succ₁ n)

data Odd where
  osucc : ∀ {n} → Even n → Odd (succ₁ n)

-- Non-mutual induction principles

Even-ind : (A : D → Set) →
           A zero →
           (∀ {n} → Odd n → A (succ₁ n)) →
           ∀ {n} → Even n → A n
Even-ind A A0 h ezero      = A0
Even-ind A A0 h (esucc On) = h On

Odd-ind : (A : D → Set) →
          (∀ {n} → Even n → A (succ₁ n)) →
          ∀ {n} → Odd n → A n
Odd-ind A h (osucc En) = h En

-- Mutual induction principles (from Coq)
Even-mutual-ind : (A B : D → Set) →
                  A zero →
                  (∀ {n} → Odd n → B n → A (succ₁ n)) →
                  (∀ {n} → Even n → A n → B (succ₁ n)) →
                  ∀ {n} → Even n → A n
Odd-mutual-ind : (A B : D → Set) →
                 A zero →
                 (∀ {n} → Odd n → B n → A (succ₁ n)) →
                 (∀ {n} → Even n → A n → B (succ₁ n)) →
                 ∀ {n} → Odd n → B n

Even-mutual-ind A B A0 h₁ h₂ ezero      = A0
Even-mutual-ind A B A0 h₁ h₂ (esucc On) = h₁ On (Odd-mutual-ind A B A0 h₁ h₂ On)

Odd-mutual-ind A B A0 h₁ h₂ (osucc En) = h₂ En (Even-mutual-ind A B A0 h₁ h₂ En)

module DisjointSum where
  -- Using a single inductive predicate on D × D (see Blanchette).

  _+_ : Set → Set → Set
  _+_ = _∨_

  data EvenOdd : D + D → Set where
    eozero :                            EvenOdd (inj₁ zero)
    eoodd  : {n : D} → EvenOdd (inj₁ n) → EvenOdd (inj₂ (succ₁ n))
    eoeven : {n : D} → EvenOdd (inj₂ n) → EvenOdd (inj₁ (succ₁ n))

  -- Induction principle
  EvenOdd-ind : (A : D + D → Set) →
                A (inj₁ zero) →
                ({n : D} → A (inj₁ n) → A (inj₂ (succ₁ n))) →
                ({n : D} → A (inj₂ n) → A (inj₁ (succ₁ n))) →
                {n : D + D} → EvenOdd n → A n
  EvenOdd-ind A A0 h₁ h₂ eozero       = A0
  EvenOdd-ind A A0 h₁ h₂ (eoodd EOn)  = h₁ (EvenOdd-ind A A0 h₁ h₂ EOn)
  EvenOdd-ind A A0 h₁ h₂ (eoeven EOn) = h₂ (EvenOdd-ind A A0 h₁ h₂ EOn)

  -------------------------------------------------------------------------
  -- From the single inductive predicate to the mutual inductive predicates

  -- Even and Odd from EvenOdd.
  Even' : D → Set
  Even' n = EvenOdd (inj₁ n)

  Odd' : D → Set
  Odd' n = EvenOdd (inj₂ n)

  -- From Even/Odd to Even'/Odd'
  Even→Even' : ∀ {n} → Even n → Even' n
  Odd→Odd'   : ∀ {n} → Odd n → Odd' n

  Even→Even' ezero = eozero
  Even→Even' (esucc On) = eoeven (Odd→Odd' On)

  Odd→Odd' (osucc En) = eoodd (Even→Even' En)

  -- From Even'/Odd' to Even/Odd
  Even'→Even : ∀ {n} → Even' n → Even n
  Odd'→Odd : ∀ {n} → Odd' n → Odd n

  -- Requires K.
  Even'→Even eozero     = ezero
  Even'→Even (eoeven h) = esucc (Odd'→Odd h)

  Odd'→Odd (eoodd h) = osucc (Even'→Even h)

  -- TODO 03 December 2012. From EvenOdd-ind to Even-mutual-ind and
  -- Odd-mutual-ind.

module FunctionSpace where
-- Using a single inductive predicate on D → D

  data EvenOdd : D → D → Set where
    eozero :                         EvenOdd zero (succ₁ zero)
    eoodd  : ∀ {m n} → EvenOdd m n → EvenOdd m (succ₁ m)
    eoeven : ∀ {m n} → EvenOdd m n → EvenOdd (succ₁ n) n

  -- Even and Odd from EvenOdd.
  -- Even' : D → Set
  -- Even' n = EvenOdd zero (succ₁ zero) ∨ EvenOdd (succ₁ n) n

  -- Odd' : D → Set
  -- Odd' n = EvenOdd n (succ₁ n)

  -- -- From Even/Odd to Even'/Odd'
  -- Even→Even' : ∀ {n} → Even n → Even' n
  -- Odd→Odd'   : ∀ {n} → Odd n → Odd' n

  -- Even→Even' ezero      = inj₁ eozero
  -- Even→Even' (esucc On) = inj₂ (eoeven (Odd→Odd' On))

  -- Odd→Odd' (osucc En) = eoodd {!!}

  -- -- From Even'/Odd' to Even/Odd
  -- Even'→Even : ∀ {n} → Even' n → Even n
  -- Odd'→Odd : ∀ {n} → Odd' n → Odd n

  -- Even'→Even (inj₁ x) = {!!}
  -- Even'→Even (inj₂ x) = {!!}

  -- Odd'→Odd h = {!!}

------------------------------------------------------------------------------
-- References:

-- • Blanchette, Jasmin Christian (2013). Relational analysis of
--   (co)inductive predicates, (co)algebraic datatypes, and
--   (co)recursive functions. In: Software Quality Journal 21.1,
--   pp. 101–126.
