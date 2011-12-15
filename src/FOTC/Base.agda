------------------------------------------------------------------------------
-- The first order theory of combinators (FOTC) base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

{-
FOTC                                  The logical framework (Agda)

* Logical constants                   * Curry-Howard isomorphism
* Equality                            * Identity type
* Term language and conversion rules  * Postulates
* Inductively defined predicates      * Inductive families
-}

module FOTC.Base where

-- We add 3 to the fixities of the standard library.
infixl 9 _·_  -- The symbol is '\cdot'.
infixr 8 _∷_
infix  8 if_then_else_

------------------------------------------------------------------------------
-- The universal domain.
open import Common.Universe public

-- The FOTC equality
-- The FOTC equality is the propositional identity on the universal domain.
import Common.Relation.Binary.PropositionalEquality
open module Eq =
  Common.Relation.Binary.PropositionalEquality.NonInductive public

-- Logical constants
open import Common.LogicalConstants public

------------------------------------------------------------------------------
-- The term language of FOTC correspond to the PCF terms.

--   t ::= x   | t · t |
--      | true | false | if
--      | zero | succ  | pred | iszero
--      | nil  | cons  | null | head   | tail
--      | loop

-- NB. We define the PCF terms as constants. After that, we will
-- define some function symbols based on these constants for
-- convenience in writing.

postulate
  _·_                     : D → D → D  -- FOTC application.
  true false if           : D          -- FOTC partial booleans.
  zero succ pred iszero   : D          -- FOTC partial natural numbers.
  nil cons head tail null : D          -- FOTC lists.
  loop                    : D          -- FOTC looping programs.

------------------------------------------------------------------------------
-- Definitions

-- We define some function symbols for convenience in writing.
abstract
  if_then_else_ : D → D → D → D
  if b then d₁ else d₂ = if · b · d₁ · d₂
  -- {-# ATP definition if_then_else_ #-}

  succ₁ : D → D
  succ₁ d = succ · d
  -- {-# ATP definition succ₁ #-}

  pred₁ : D → D
  pred₁ d = pred · d
  -- {-# ATP definition pred₁ #-}

  iszero₁ : D → D
  iszero₁ d = iszero · d
  -- {-# ATP definition iszero₁ #-}

  [] : D
  [] = nil
  -- {-# ATP definition [] #-}

  _∷_  : D → D → D
  x ∷ xs = cons · x · xs
  -- {-# ATP definition _∷_ #-}

  head₁ : D → D
  head₁ xs = head · xs
  -- {-# ATP definition head₁ #-}

  tail₁ : D → D
  tail₁ xs = tail · xs
  -- {-# ATP definition tail₁ #-}

  null₁ : D → D
  null₁ xs = null · xs
  -- {-# ATP definition null₁ #-}

------------------------------------------------------------------------------
-- Conversion rules

-- The conversion relation _conv_ satifies (Aczel 1977. The strength
-- of Martin-Löf's intuitionistic type theory with one universe,
-- p. 8).
--
-- x conv y <=> FOTC ⊢ x ≡ y,
--
-- therefore, we introduce the conversion rules as FOL non-logical
-- axioms.

-- N.B. Looking for an optimization for the ATPs, we write the
-- conversion rules on the defined function symbols instead of on the
-- PCF constants.

-- Conversion rules for booleans.
postulate
  -- if-true  : ∀ d₁ {d₂} → if · true  · d₁ · d₂ ≡ d₁
  -- if-false : ∀ {d₁} d₂ → if · false · d₁ · d₂ ≡ d₂
  if-true  : ∀ d₁ {d₂} → if true  then d₁ else d₂ ≡ d₁
  if-false : ∀ {d₁} d₂ → if false then d₁ else d₂ ≡ d₂
{-# ATP axiom if-true if-false #-}

-- Conversion rules for pred.
postulate
  -- N.B. We don't need this equation.
  -- pred-0 :       pred zero     ≡ zero
  -- pred-S : ∀ d → pred · (succ · d) ≡ d
  pred-S : ∀ d → pred₁ (succ₁ d) ≡ d
{-# ATP axiom pred-S #-}

-- Conversion rules for iszero.
postulate
  -- iszero-0 :       iszero · zero       ≡ true
  -- iszero-S : ∀ d → iszero · (succ · d) ≡ false
  iszero-0 :       iszero₁ zero      ≡ true
  iszero-S : ∀ d → iszero₁ (succ₁ d) ≡ false
{-# ATP axiom iszero-0 iszero-S #-}

-- Conversion rules for null.
postulate
  -- null-[] :          null · nil             ≡ true
  -- null-∷  : ∀ x xs → null · (cons · x · xs) ≡ false
  null-[] :          null₁ []       ≡ true
  null-∷  : ∀ x xs → null₁ (x ∷ xs) ≡ false

-- Conversion rule for head.
postulate
--  head-∷ : ∀ x xs → head · (cons · x · xs) ≡ x
  head-∷ : ∀ x xs → head₁ (x ∷ xs) ≡ x
{-# ATP axiom head-∷ #-}

-- Conversion rule for tail.
postulate
--  tail-∷ : ∀ x xs → tail · (cons · x · xs) ≡ xs
  tail-∷ : ∀ x xs → tail₁ (x ∷ xs) ≡ xs
{-# ATP axiom tail-∷ #-}

-- Conversion rule for loop.
-- The equation loop-eq adds anything to the logic (because
-- reflexivity is already an axiom of equality), therefore we won't
-- add this equation as a FOL axiom.
postulate loop-eq : loop ≡ loop

------------------------------------------------------------------------------
-- Discrimination rules

postulate
  true≠false : ¬ (true ≡ false)
--  0≠S        : ∀ {d} → ¬ (zero ≡ succ · d)
  0≠S        : ∀ {d} → ¬ (zero ≡ succ₁ d)
{-# ATP axiom true≠false 0≠S #-}
