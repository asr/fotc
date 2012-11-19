------------------------------------------------------------------------------
-- Definition of mutual inductive predicates
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}

module FOTC.MutualInductivePredicates where

open import FOTC.Base

-- References:

-- · Jasmin Christian Blanchette. Relational analysis of (co)inductive
--   predicates, (co)algebraic datatypes, and (co)recursive
--   functions. To appear in a special issue of the Software Quality
--   Journal.

------------------------------------------------------------------------------
-- Using mutual inductive predicates

data Even : D → Set
data Odd  : D → Set

data Even where
  ezero : Even zero
  esucc : ∀ {n} → Odd n → Even (succ₁ n)

data Odd where
  osucc : ∀ {n} → Even n → Odd (succ₁ n)

module DisjointSum where
  -- Using a single inductive predicate on D × D (see Blanchette).

  _+_ : Set → Set → Set
  _+_ = _∨_

  data EvenOdd : D + D → Set where
    eozero :                            EvenOdd (inj₁ zero)
    eoodd  : ∀ {n} → EvenOdd (inj₁ n) → EvenOdd (inj₂ (succ₁ n))
    eoeven : ∀ {n} → EvenOdd (inj₂ n) → EvenOdd (inj₁ (succ₁ n))

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
