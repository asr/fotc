------------------------------------------------------------------------------
-- The first-order theory of combinators (FOTC) base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

{-
FOTC                                  The logical framework (Agda)

* Logical constants                   * Curry-Howard isomorphism
* Equality                            * Identity type
* Term language and conversion rules  * Postulates
* Inductively defined predicates      * Inductive families
* Co-inductively defined predicates   * Greatest fixed-points
-}

module FOTC.Base where

-- We add 3 to the fixities of the Agda standard library 0.6 (see
-- Algebra.agda).
infixl 9 _·_
-- We add 8 to the fixity of the Agda standard library 0.6 (see
-- Data/Bool.agda).
infix 8 if_then_else_

------------------------------------------------------------------------------
-- First-order logic with equality.
open import Common.FOL.FOL-Eq public

-- Common definitions.
open import Common.DefinitionsATP public

------------------------------------------------------------------------------
-- The term language of FOTC

--   t ::= x   | t · t |
--      | true | false | if
--      | 0    | succ  | pred | iszero

postulate
  _·_                    : D → D → D  -- FOTC application.
  true false if          : D          -- FOTC partial Booleans.
  zero succ pred iszero  : D          -- FOTC partial natural numbers.

------------------------------------------------------------------------------
-- Definitions

-- We define some function symbols for convenience in writing and
-- looking for an optimization for the ATPs.

-- 2012-03-20. The definitions are inside an abstract block because
-- the conversion rules (see below) are based on them, so we want to
-- avoid their expansion.

abstract
  if_then_else_ : D → D → D → D
  if b then t else t' = if · b · t · t'
  -- {-# ATP definition if_then_else_ #-}

  succ₁ : D → D
  succ₁ n = succ · n
  -- {-# ATP definition succ₁ #-}

  pred₁ : D → D
  pred₁ n = pred · n
  -- {-# ATP definition pred₁ #-}

  iszero₁ : D → D
  iszero₁ n = iszero · n
  -- {-# ATP definition iszero₁ #-}

------------------------------------------------------------------------------
-- Conversion rules

-- The conversion relation _conv_ satifies (Aczel 1977, p. 8)
--
-- x conv y <=> FOTC ⊢ x ≡ y,
--
-- therefore, we introduce the conversion rules as non-logical axioms.

-- N.B. Looking for an optimization for the ATPs, we write the
-- conversion rules on the defined function symbols instead of on the
-- term constants.

-- Conversion rules for Booleans.
-- if-true  : ∀ t {t'} → if · true  · t · t' ≡ t
-- if-false : ∀ {t} t' → if · false · t · t' ≡ t'
postulate
  if-true  : ∀ t {t'} → if true then t else t'  ≡ t
  if-false : ∀ {t} t' → if false then t else t' ≡ t'
{-# ATP axiom if-true if-false #-}

-- Conversion rules for pred.
-- pred-0 :       pred · zero     ≡ zero
-- pred-S : ∀ n → pred · (succ · n) ≡ n
postulate
  pred-0 : pred₁ zero            ≡ zero
  pred-S : ∀ n → pred₁ (succ₁ n) ≡ n
{-# ATP axiom pred-0 pred-S #-}

-- Conversion rules for iszero.
-- iszero-0 :       iszero · zero       ≡ true
-- iszero-S : ∀ n → iszero · (succ · n) ≡ false
postulate
  iszero-0 : iszero₁ zero            ≡ true
  iszero-S : ∀ n → iszero₁ (succ₁ n) ≡ false
{-# ATP axiom iszero-0 iszero-S #-}

------------------------------------------------------------------------------
-- Discrimination rules

--  0≢S : ∀ {n} → zero ≢ succ · n
postulate
  t≢f : true ≢ false
  0≢S : ∀ {n} → zero ≢ succ₁ n
{-# ATP axiom t≢f 0≢S #-}

------------------------------------------------------------------------------
-- References
--
-- Aczel, Peter (1977). The Strength of MartinLöf’s Intuitionistic
-- Type Theory with One Universe. In: Proc. of the Symposium on
-- Mathematical Logic (Oulu, 1974). Ed. by Miettinen, S. and Väänanen,
-- J. Report No. 2, Department of Philosophy, University of Helsinki,
-- Helsinki, pp. 1–32.
