------------------------------------------------------------------------------
-- The LTC-PCF base
------------------------------------------------------------------------------

{-
LTC-PCF                               The logical framework (Agda)

* Logical constants                   * Curry-Howard isomorphism
* Equality                            * Identity type
* Term language and conversion rules  * Postulates
* Inductively defined predicates      * Inductive families
-}

module LTC-PCF.Base where

-- We add 3 to the fixities of the standard library.
infixl 9 _·_  -- The symbol is '\cdot'.
infix  8 if_then_else_

------------------------------------------------------------------------------
-- The universal domain.
open import Common.Universe public

-- The LTC-PCF equality
-- The LTC-PCF equality is the propositional identity on the universal domain.
import Common.Relation.Binary.PropositionalEquality
open module Eq =
  Common.Relation.Binary.PropositionalEquality.NonInductive public

-- Logical constants
open import Common.LogicalConstants public

------------------------------------------------------------------------------
-- The term language of LTC-PCF correspond to the PCF terms.

--   t ::= x   | t · t | λ x.t
--      | true | false | if
--      | zero | succ  | pred | iszero
--      | fix

-- NB. We define the PCF terms as constants. After that, we will
-- define some function symbols based on these constants for
-- convenience in writing.

postulate
  _·_                   : D → D → D    -- LTC-PCF application.
  lam                   : (D → D) → D  -- LTC-PCF abstraction.
  true false if         : D            -- LTC-PCF partial booleans.
  zero succ pred iszero : D            -- LTC-PCF partial natural numbers.
  fix                   : D            -- LTC fixed point operator.

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

  fix₁ : (D → D) → D
  fix₁ f = fix · lam f

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
  -- pred-0 : ∀ d → pred · zero ≡ zero
  -- pred-S : ∀ d → pred · (succ · d) ≡ d

 -- N.B. We don't need this equation in the FOTC.
  pred-0 : pred₁ zero ≡ zero
  pred-S : ∀ d → pred₁ (succ₁ d) ≡ d
{-# ATP axiom pred-0 pred-S #-}

-- Conversion rules for iszero.
postulate
  -- iszero-0 :       iszero · zero       ≡ true
  -- iszero-S : ∀ d → iszero · (succ · d) ≡ false
  iszero-0 :       iszero₁ zero      ≡ true
  iszero-S : ∀ d → iszero₁ (succ₁ d) ≡ false
{-# ATP axiom iszero-0 iszero-S #-}

-- Conversion rule for the abstraction and the application.
postulate beta : (f : D → D)(a : D) → lam f · a ≡ f a
{-# ATP axiom beta #-}

-- Conversion rule for the fixed pointed operator.
postulate
  fix-f : (f : D → D) → fix₁ f ≡ f (fix₁ f)
{-# ATP axiom fix-f #-}

------------------------------------------------------------------------------
-- Discrimination rules

postulate
  true≠false : ¬ (true ≡ false)
--  0≠S        : ∀ {d} → ¬ (zero ≡ succ · d)
  0≠S        : ∀ {d} → ¬ (zero ≡ succ₁ d)
{-# ATP axiom true≠false 0≠S #-}
