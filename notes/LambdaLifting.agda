------------------------------------------------------------------------------
-- Example of lambda-lifting
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --universal-quantified-functions #-}
{-# OPTIONS --without-K #-}

module LambdaLifting where

infixl 9 _·_
infix  8 if_then_else_
infix  7 _≡_

infixl 10 _*_
infixl 9  _+_

------------------------------------------------------------------------------

postulate
  D                : Set
  zero true false  : D
  succ iszero pred : D → D
  _·_              : D → D → D
  if_then_else_    : D → D → D → D
  lam fix          : (D → D) → D

data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- Conversion rules

-- Conversion rules for Booleans.
postulate
  if-true  : ∀ d₁ {d₂} → if true then d₁ else d₂  ≡ d₁
  if-false : ∀ {d₁} d₂ → if false then d₁ else d₂ ≡ d₂
{-# ATP axiom if-true if-false #-}

-- Conversion rules for pred.
postulate
  -- N.B. We don't need this equation.
  -- pred-0 :       pred zero     ≡ zero
  pred-S : ∀ d → pred (succ d) ≡ d
{-# ATP axiom pred-S #-}

-- Conversion rules for iszero.
postulate
  iszero-0 :       iszero zero     ≡ true
  iszero-S : ∀ d → iszero (succ d) ≡ false
{-# ATP axiom iszero-0 iszero-S #-}

-- Conversion rule for the λ-abstraction and the application.
postulate beta : ∀ f a → lam f · a ≡ f a
{-# ATP axiom beta #-}

-- Conversion rule for the fixed-pointed operator.
postulate fix-eq : ∀ f → fix f ≡ f (fix  f)
{-# ATP axiom fix-eq #-}

postulate
  _+_  : D → D → D
  +-0x : ∀ d → zero + d     ≡ d
  +-Sx : ∀ d e → succ d + e ≡ succ (d + e)
{-# ATP axiom +-0x +-Sx #-}

postulate
  _*_  : D → D → D
  *-0x : ∀ d → zero * d ≡ zero
  *-Sx : ∀ d e → succ d * e ≡ e + d * e
{-# ATP axiom *-0x *-Sx #-}

------------------------------------------------------------------------------
-- The original fach
-- fach : D → D
-- fach f = lam (λ n → if (iszero n) then (succ zero) else n * (f · (pred n)))

-- Lambda-lifting via super-combinators (Hughes. Super-combinators. 1982).

α : D → D → D
α f n = if (iszero n) then (succ zero) else n * (f · (pred n))
{-# ATP definition α #-}

fach : D → D
fach f = lam (α f)
{-# ATP definition fach #-}

fac : D → D
fac n = fix fach · n
{-# ATP definition fac #-}

postulate fac0 : fac zero ≡ succ zero
{-# ATP prove fac0 #-}

postulate fac1 : fac (succ zero) ≡ succ zero
{-# ATP prove fac1 #-}

postulate fac2 : fac (succ (succ zero)) ≡ succ (succ zero)
{-# ATP prove fac2 #-}

------------------------------------------------------------------------------
-- Ouput:
--
-- $ agda2atp -inotes --non-fol-function notes/LambdaLifting.agda
-- Proving the conjecture in /tmp/LambdaLifting/95-fac1.tptp ...
-- E 1.6 Tiger Hill proved the conjecture in /tmp/LambdaLifting/95-fac1.tptp
-- Proving the conjecture in /tmp/LambdaLifting/99-fac2.tptp ...
-- E 1.6 Tiger Hill proved the conjecture in /tmp/LambdaLifting/99-fac2.tptp
-- Proving the conjecture in /tmp/LambdaLifting/91-fac0.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture in /tmp/LambdaLifting/91-fac0.tptp
