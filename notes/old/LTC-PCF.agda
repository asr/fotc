module LTC-PCF where

module Core where

{-
Agda as a logical framework for LTC-PCF

LTC-PCF                              Agda
* Logical constants              * Curry-Howard isomorphism
* Equality                       * Identity type
* Term language                  * Postulates
* Inductive predicates           * Inductive families
-}

-- Fixity declarations (precedence level and associativity)
-- Agda default: infix 20

infixl 80 _`_
infixl 60 _∧_
infixl 50 _∨_
infix  40 if#_then_else_
infix  30 _==_

-------------------------------------------------------------------------
-- Equality: identity type
-------------------------------------------------------------------------

-- The identity type
data _==_ {A : Set} : A -> A -> Set where
  ==-refl : {x : A} -> x == x

==-subst : {A : Set}(P : A -> Set){x y : A} -> x == y -> P x -> P y
==-subst P ==-refl px = px

==-sym : {A : Set} {x y : A} -> x == y ->  y == x
==-sym ==-refl = ==-refl

==-trans : {A : Set} {x y z : A} -> x == y -> y == z -> x == z
==-trans ==-refl y==z  = y==z

-------------------------------------------------------------------------
-- Logical constants: Curry-Howard isomorphism
-------------------------------------------------------------------------

-- The false type
data ⊥ : Set where

⊥-elim : {A : Set} -> ⊥ -> A
⊥-elim ()

¬ : Set -> Set
¬ A = A -> ⊥

-- The disjunction type ('\vee', not 'v')
data _∨_ (A B : Set) : Set where
  ∨-il : A -> A ∨ B
  ∨-ir : B -> A ∨ B

∨-elim : {A B C : Set} -> (A -> C) -> (B -> C) -> A ∨ B -> C
∨-elim f g (∨-il a) = f a
∨-elim f g (∨-ir b) = g b

-- The conjunction type
data _∧_ (A B : Set) : Set where
  ∧-i : A -> B -> A ∧ B

∧-fst : {A B : Set} -> A ∧ B -> A
∧-fst (∧-i a b) = a

∧-snd : {A B : Set} -> A ∧ B -> B
∧-snd (∧-i a b) = b

-- The existential quantifier type
data ∃ (A : Set)(P : A -> Set) : Set where
  ∃-i : (witness : A)  -> P witness -> ∃ A P

∃-fst : {A : Set}{P : A -> Set} -> ∃ A P -> A
∃-fst (∃-i x px) = x

∃-snd : {A : Set}{P : A -> Set} -> (x-px : ∃ A P) -> P (∃-fst x-px)
∃-snd (∃-i x px) = px

-- The implication and the universal quantifier
-- We use Agda (dependent) function type

-------------------------------------------------------------------------
--  The term language: postulates
-------------------------------------------------------------------------

{-
D : a universal domain of terms

Pre-types (or weak types): Agda's simple type lambda calculus on 'D'

              T ::= D | T -> T
                t := x | \x -> t | t t | c (constants)

-}

-------------------------
-- The universal domain

postulate D : Set

--------------------
-- Constants terms

postulate

  -- LTC-PCF booleans
  true#          : D
  false#         : D
  if#_then_else_ : D -> D -> D -> D

  -- LTC-PCF natural numbers
  -- We will refer to these partial numbers as 'N#'
  zero# : D
  suc#  : D -> D
  rec#  : D -> D -> (D -> D -> D) -> D

  -- LTC-PCF abstraction and application
  λ   : (D -> D) -> D
  -- Left associative aplication operator
  _`_ : D -> D -> D

----------------------
-- Conversion rules

postulate
  -- Conversion rules for booleans
  CB1 : (a : D){b : D} -> if# true# then a else b == a
  CB2 : {a : D}(b : D) -> if# false# then a else b == b

  -- Conversion rules for natural numbers
  CN1 : (a : D){f : D -> D -> D} -> rec# zero# a f == a
  CN2 : (a n : D)(f : D -> D -> D) ->
        rec# (suc# n) a f == f n (rec# n a f)

  -- Conversion rule for the abstraction and the application
  beta : (f : D -> D)(a : D) -> (λ f) ` a == f a

--------------------------------------------------------------
-- Inductive predicate for natural numbers : Inductive family
--------------------------------------------------------------
-- The inductive predicate 'N' represents the type of the natural
-- numbers. They are a subset of 'D'.

-- The natural numbers type
data N : D -> Set where
  N-zero : N zero#
  N-suc : {n : D} -> N n -> N (suc# n)

-- Induction principle on 'N'  (elimination rule)
N-ind : (P : D -> Set) ->
        P zero# ->
        ({n : D} -> N n -> P n -> P (suc#  n)) ->
        {n : D} -> N n -> P n
N-ind P p0 h N-zero     = p0
N-ind P p0 h (N-suc Nn) = h Nn (N-ind P  p0  h Nn)



module Recursive-Functions where

  -- We define some primitive recursive functions via LTC-PCF terms

  open Core

  import Equality-Reasoning
  open module ER-Recursive-Functions =
              Equality-Reasoning (_==_ {D}) ==-refl ==-trans

   ------------------------------------------------------------------------
  -- Remark: We are using Agda's definitional equality '=' as
  -- LTC-PCF's definitional equality

  -- Fixity declarations (precedence level and associativity)
  -- Agda default: infix 20

  infixl 70 _*_
  infixl 60 _+_ _-_

  _+_ : D -> D -> D
  m + n = rec# n m (\x y -> suc# y)

  -- recursion on the second argument
  _*_ : D -> D -> D
  m * n = rec# n zero# (\x y -> y + n)

  pred : D -> D
  pred n = rec# n zero# (\x y -> x)

  -- m - 0        = m
  -- m - (succ n) = pred (m - n)
  _-_ : D -> D -> D
  m - n = rec# n m (\x y -> pred y)

  or : D -> D -> D
  or a b = if#  a then true# else b

  isZero : D -> D
  isZero n = rec# n true# (\x y -> false#)

  -- The function 'equi n' return a function which establish if an
  -- argument 'm' is equal to 'n'
  -- equi zero     = \m -> isZero m
  -- equi (succ n) = \m -> case m of
  --                         zero -> false
  --                         (succ m') -> (equi n) m

  equi : D -> D
  equi n = rec# n  (λ (\m -> isZero m))
               (\x y -> λ (\m -> rec# m  false#  (\m' z -> y ` m')))

  -- equality on N#
  eq : D -> D -> D
  eq m n = (equi n) ` m

  -- inequality on N#
  -- lt m 0        = false#
  -- lt m (succ n) = (lt m n) ∨ (m = n)
  lt : D -> D -> D
  lt m n = rec# n false# (\x y -> or y  (eq m  x))

  -- inequality on N#
  gt : D -> D -> D
  gt m n = lt n m
