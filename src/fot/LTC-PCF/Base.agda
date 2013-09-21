------------------------------------------------------------------------------
-- The LTC-PCF base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

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
-- First-order logic with equality.
open import Common.FOL.FOL-Eq public

-- Common definitions.
open import Common.DefinitionsI public

------------------------------------------------------------------------------
-- The term language of LTC-PCF correspond to the PCF terms.

--   t ::= x
--      | t · t
--      | λ x.t
--      | fix x.t
--      | true | false | if
--      | zero | succ  | pred | iszero

-- NB. We define the PCF terms as constants. After that, we will
-- define some function symbols based on these constants for
-- convenience in writing.

postulate
  _·_                   : D → D → D    -- LTC-PCF application.
  lam                   : (D → D) → D  -- LTC-PCF λ-abstraction.
  fix                   : (D → D) → D  -- LTC-PCF fixed-point operator.
  true false if         : D            -- LTC-PCF partial Booleans.
  zero succ pred iszero : D            -- LTC-PCF partial natural numbers.

------------------------------------------------------------------------------
-- Definitions

-- We define some function symbols for convenience in writing.
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

-- The conversion relation _conv_ satifies (Aczel 1977. The strength
-- of Martin-Löf's intuitionistic type theory with one universe,
-- p. 8).
--
-- x conv y <=> FOTC ⊢ x ≡ y,
--
-- therefore, we introduce the conversion rules as non-logical axioms.

-- N.B. We write the conversion rules on the defined function symbols
-- instead of on the PCF constants.

-- Conversion rule for the λ-abstraction and the application.
postulate beta : ∀ f a → lam f · a ≡ f a

-- Conversion rule for the fixed-pointed operator.
postulate fix-eq : ∀ f → fix f ≡ f (fix f)

-- Conversion rules for Booleans.
postulate
  -- if-true  : ∀ t {t'} → if · true  · t · t' ≡ t
  -- if-false : ∀ {t} t' → if · false · t · t' ≡ t'
  if-true  : ∀ t {t'} → if true then t else t'  ≡ t
  if-false : ∀ {t} t' → if false then t else t' ≡ t'

-- Conversion rules for pred.
postulate
  -- pred-0 : pred · zero ≡ zero
  -- pred-S : ∀ d → pred · (succ · d) ≡ d

 -- N.B. We don't need this equation in FOTC.
  pred-0 : pred₁ zero            ≡ zero
  pred-S : ∀ n → pred₁ (succ₁ n) ≡ n

-- Conversion rules for iszero.
postulate
  -- iszero-0 :       iszero · zero       ≡ true
  -- iszero-S : ∀ d → iszero · (succ · d) ≡ false
  iszero-0 : iszero₁ zero            ≡ true
  iszero-S : ∀ n → iszero₁ (succ₁ n) ≡ false

------------------------------------------------------------------------------
-- Discrimination rules

postulate
  t≢f : true ≢ false
  -- 0≢S : ∀ {d} → zero ≢ succ · d
  0≢S : ∀ {n} → zero ≢ succ₁ n
