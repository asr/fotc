------------------------------------------------------------------------------
-- The LTC core
------------------------------------------------------------------------------
{-

LTC                              Agda
* Logical constants              * Curry-Howard isomorphism
* Equality                       * Identity type
* Term language                  * Postulates
* Inductive predicates           * Inductive families
-}

module LTC.Minimal where

infixl 6 _∙_
infixr 5 _∷_
infix  5 if_then_else_
infix  4 _≡_

------------------------------------------------------------------------------
-- The universal domain

-- N.B. The following module is exported by this module.
open import LTC.Minimal.Core public

------------------------------------------------------------------------------
-- The term language of LTC correspond to the PCF terms.

--   t ::= x    | t t    | \x → t
--      | true  | false  | if t then t else t
--      | 0     | succ t | pred t             | isZero t
--      | []    | _∷_    | head               | tail
--      | fix t
--      | error

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
  lam : (D → D) → D

  -- LTC application.
  -- The Agda application has higher precedence level than LTC application.
  _∙_ : D → D → D

  -- LTC error.
  error : D

  -- LTC fixed point operator.
  fix : (D → D) → D
  -- fixFO  : D

  -- LTC lists.
  []   : D
  _∷_  : D → D → D
  head : D → D
  tail : D → D

------------------------------------------------------------------------------
-- The LTC equality is the propositional identity on 'D'.

-- The identity type on D.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- Identity properties

sym : {x y : D} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : D} → x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z

-- The substitution is defined in LTC.MinimalER.

------------------------------------------------------------------------------
-- Logical constants: Curry-Howard isomorphism

-- The LTC logical constants are the type theory logical constants via
-- the Curry-Howard isomorphism.  For the implication and the
-- universal quantifier we use the Agda (dependent) function type.

-- N.B. The following modules are exported by this module.
open import Lib.Data.Empty       public
open import Lib.Data.Product     public
open import Lib.Data.Sum         public
-- open import Lib.Data.Unit        public
open import Lib.Relation.Nullary public
open import LTC.Data.Product     public

------------------------------------------------------------------------------
-- Conversion rules

postulate
  -- Conversion rules for booleans.
  if-true  : (d₁ : D){d₂ : D} →  if true then d₁ else d₂ ≡ d₁
  if-false : {d₁ : D}(d₂ : D) → if false then d₁ else d₂ ≡ d₂
{-# ATP axiom if-true #-}
{-# ATP axiom if-false #-}

postulate
  -- Conversion rules for pred.
  pred-0 :           pred zero     ≡ zero
  pred-S : (n : D) → pred (succ n) ≡ n
{-# ATP axiom pred-0 #-}
{-# ATP axiom pred-S #-}

postulate
  -- Conversion rules for isZero.
  isZero-0 :           isZero zero     ≡ true
  isZero-S : (n : D) → isZero (succ n) ≡ false
{-# ATP axiom isZero-0 #-}
{-# ATP axiom isZero-S #-}

postulate
  -- Conversion rule for the abstraction and the application.
  beta : (f : D → D) → (a : D) → (lam f) ∙ a ≡ f a
{-# ATP axiom beta #-}

postulate
  -- Conversion rule for the fixed pointed operator.
  fix-f : (f : D → D) → fix f ≡ f (fix  f)
  -- cFixFO : (f : D) → fixFO ∙ f  ≡ f ∙ (fixFO ∙ f)
{-# ATP axiom fix-f #-}

postulate
  -- Conversion rule for head.
  head-∷ : (x xs : D) → head (x ∷ xs) ≡ x
{-# ATP axiom head-∷ #-}

postulate
  -- Conversion rule for tail.
  tail-∷ : (x xs : D) → tail (x ∷ xs) ≡ xs
{-# ATP axiom tail-∷ #-}

------------------------------------------------------------------------------
-- Discrimination rules

postulate
  true≠false : ¬ (true ≡ false)
  0≠S        : {d : D} → ¬ (zero ≡ succ d)
{-# ATP axiom true≠false #-}
{-# ATP axiom 0≠S #-}
