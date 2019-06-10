------------------------------------------------------------------------------
-- The first-order theory of combinators (FOTC) base
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

{-
FOTC                                  The logical framework (Agda)

* Logical constants                   * Curry-Howard isomorphism
* Equality                            * Identity type
* Term language and conversion rules  * Postulates
* Inductively defined predicates      * Inductive families
* Co-inductively defined predicates   * Greatest fixed-points
-}

module Interactive.FOTC.Base where

-- First-order logic with equality.
open import Common.FOL.FOL-Eq public

-- Common definitions.
open import Interactive.Common.Definitions public

infixl 7 _·_
infix  0 if_then_else_

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

  succ₁ : D → D
  succ₁ n = succ · n

  pred₁ : D → D
  pred₁ n = pred · n

  iszero₁ : D → D
  iszero₁ n = iszero · n

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
  if-true  : ∀ t {t'} → (if true then t else t')  ≡ t
  if-false : ∀ {t} t' → (if false then t else t') ≡ t'

-- Conversion rules for pred.
-- pred-0 :       pred · zero     ≡ zero
-- pred-S : ∀ n → pred · (succ · n) ≡ n
postulate
  pred-0 : pred₁ zero            ≡ zero
  pred-S : ∀ n → pred₁ (succ₁ n) ≡ n

-- Conversion rules for iszero.
-- iszero-0 :       iszero · zero       ≡ true
-- iszero-S : ∀ n → iszero · (succ · n) ≡ false
postulate
  iszero-0 : iszero₁ zero            ≡ true
  iszero-S : ∀ n → iszero₁ (succ₁ n) ≡ false

------------------------------------------------------------------------------
-- Discrimination rules

--  0≢S : ∀ {n} → zero ≢ succ · n
postulate
  t≢f : true ≢ false
  0≢S : ∀ {n} → zero ≢ succ₁ n

------------------------------------------------------------------------------
-- References
--
-- Aczel, Peter (1977). The Strength of MartinLöf’s Intuitionistic
-- Type Theory with One Universe. In: Proc. of the Symposium on
-- Mathematical Logic (Oulu, 1974). Ed. by Miettinen, S. and Väänanen,
-- J. Report No. 2, Department of Philosophy, University of Helsinki,
-- Helsinki, pp. 1–32.
