------------------------------------------------------------------------------
-- Agda as a logical framework for LTC
------------------------------------------------------------------------------
{-

LTC                              Agda
* Logical constants              * Curry-Howard isomorphism
* Equality                       * Identity type
* Term language                  * Postulates
* Inductive predicates           * Inductive families
-}

------------------------------------------------------------------------------

module LTC.Minimal where

-- Standard library imports
-- open import Data.Fin using ( Fin )
-- open import Data.Nat using ( ℕ )
-- open import Data.String
-- open import Relation.Binary.PropositionalEquality
-- open ≡-Reasoning

infixl 6 _∙_
infix  5 if_then_else_
infix  4 _≡_

------------------------------------------------------------------------------
-- The universal domain
------------------------------------------------------------------------------

-- N.B. The following module is exported by this module.
open import LTC.Minimal.Core public

------------------------------------------------------------------------------
-- The term language
------------------------------------------------------------------------------

-- The term language of LTC correspond to the PCF terms

--   t ::= x | t t | \x -> t
--           | true | false | if t then t else t
--           | 0 | succ t | pred t | isZero t
--           | error
--           | fix t

postulate

  -- LTC partial booleans.
  true          : D
  false         : D
  if_then_else_ : D → D → D → D
  -- LTC partial natural numbers.
  zero   : D
  succ   : D → D
  pred   : D → D
  isZero : D → D
  -- LTC abstraction.
  lam    : (D → D) → D
  -- LTC application
  -- Left associative aplication operator
  -- The Agda application has higher precedence level than LTC application
  _∙_    : D → D → D
  -- LTC error
  error  : D
  -- LTC fixed point operator
  fix    : (D → D) → D
  -- fixFO  : D

------------------------------------------------------------------------------
-- Equality: identity type
------------------------------------------------------------------------------

-- The LTC's equality is the propositional identity on 'D'.

-- The identity type.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

------------------------------------------------------------------------------
-- Logical constants: Curry-Howard isomorphism
------------------------------------------------------------------------------

-- The LTC's logical constants are the type theory's logical
-- constants via the Curry-Howard isomorphism.
-- For the implication and the universal quantifier
-- we use Agda (dependent) function type.

-- N.B. The following modules are exported by this module.
open import LTC.Data.Product public
open import MyStdLib.Data.Empty public
open import MyStdLib.Data.Product public
open import MyStdLib.Data.Sum public
open import MyStdLib.Relation.Nullary public

------------------------------------------------------------------------------
-- Conversion rules
------------------------------------------------------------------------------

postulate
  -- Conversion rules for booleans.
  cB₁ : (d₁ : D){d₂ : D} → if true  then d₁ else d₂ ≡ d₁
  cB₂ : {d₁ : D}(d₂ : D) → if false then d₁ else d₂ ≡ d₂
{-# ATP axiom cB₁ #-}
{-# ATP axiom cB₂ #-}

postulate
  -- Conversion rules for pred.
  cP₁ : pred zero               ≡ zero
  cP₂ : (n : D) → pred (succ n) ≡ n
{-# ATP axiom cP₁ #-}
{-# ATP axiom cP₂ #-}

postulate
  -- Conversion rules for isZero
  cZ₁ : isZero zero               ≡ true
  cZ₂ : (n : D) → isZero (succ n) ≡ false
{-# ATP axiom cZ₁ #-}
{-# ATP axiom cZ₂ #-}

postulate
  -- Conversion rule for the abstraction and the application.
  cBeta : (f : D → D) → (a : D) → (lam f) ∙ a ≡ f a
{-# ATP axiom cBeta #-}

postulate
  -- Conversion rule for the fixed pointed operator.
  cFix   : (f : D → D) → fix f ≡ f (fix  f)
  -- cFixFO : (f : D) → fixFO ∙ f  ≡ f ∙ (fixFO ∙ f)
{-# ATP axiom cFix #-}

------------------------------------------------------------------------------
-- Discrimination rules
------------------------------------------------------------------------------

postulate
  true≠false : ¬ (true ≡ false)
  0≠S        : {d : D} → ¬ ( zero ≡ succ d)
{-# ATP axiom true≠false #-}
{-# ATP axiom 0≠S #-}
