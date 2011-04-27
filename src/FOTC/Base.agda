------------------------------------------------------------------------------
-- The first order theory of combinators (FOTC) base
------------------------------------------------------------------------------
{-

FOTC                              Agda
* Logical constants              * Curry-Howard isomorphism
* Equality                       * Identity type
* Term language                  * Postulates
* Inductive predicates           * Inductive families
-}

module FOTC.Base where

infixl 9 _·_  -- The symbol is '\cdot'.
infixr 8 _∷_  -- We add 3 to the fixities of the standard library.
infix  8 if_then_else_

------------------------------------------------------------------------------
-- The universal domain.
open import Common.Universe public

-- The FOTC equality
-- The FOTC equality is the propositional identity on the universal domain.
open import Common.Relation.Binary.PropositionalEquality public

-- Logical constants
open import Common.LogicalConstants public

------------------------------------------------------------------------------
-- The term language of FOTC correspond to the PCF terms.

--   t ::= x    | t t    |
--      | true  | false  | if t then t else t
--      | 0     | succ t | pred t             | isZero t
--      | []    | _∷_    | null               | head     | tail

postulate

  -- FOTC partial booleans.
  true          : D
  false         : D
  if_then_else_ : D → D → D → D

  -- FOTC partial natural numbers.
  zero   : D
  succ   : D → D
  pred   : D → D
  isZero : D → D

  -- FOTC application.
  -- The Agda application has higher precedence level than FOTC application.
  _·_ : D → D → D

  -- FOTC lists.
  []   : D
  _∷_  : D → D → D
  null : D → D
  head : D → D
  tail : D → D

------------------------------------------------------------------------------
-- Conversion rules

postulate
  -- Conversion rules for booleans.
  if-true  : ∀ d₁ {d₂} → if true then d₁ else d₂  ≡ d₁
  if-false : ∀ {d₁} d₂ → if false then d₁ else d₂ ≡ d₂
{-# ATP axiom if-true #-}
{-# ATP axiom if-false #-}

postulate
  -- Conversion rules for pred.
  -- N.B. We don't need this equation.
  -- pred-0 :       pred zero     ≡ zero
  pred-S : ∀ d → pred (succ d) ≡ d
{-# ATP axiom pred-S #-}

postulate
  -- Conversion rules for isZero.
  isZero-0 :       isZero zero     ≡ true
  isZero-S : ∀ d → isZero (succ d) ≡ false
{-# ATP axiom isZero-0 #-}
{-# ATP axiom isZero-S #-}

postulate
  -- Conversion rules for null.
  null-[] :          null []       ≡ true
  null-∷  : ∀ x xs → null (x ∷ xs) ≡ false

postulate
  -- Conversion rule for head.
  head-∷ : ∀ x xs → head (x ∷ xs) ≡ x
{-# ATP axiom head-∷ #-}

postulate
  -- Conversion rule for tail.
  tail-∷ : ∀ x xs → tail (x ∷ xs) ≡ xs
{-# ATP axiom tail-∷ #-}

------------------------------------------------------------------------------
-- Discrimination rules

postulate
  true≠false : ¬ (true ≡ false)
  0≠S        : ∀ {d} → ¬ (zero ≡ succ d)
{-# ATP axiom true≠false #-}
{-# ATP axiom 0≠S #-}
