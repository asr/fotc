------------------------------------------------------------------------------
-- Addition as a function constant
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.AddConstant where

------------------------------------------------------------------------------
-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Algebra.agda and Relation/Binary/Core.agda).
infixl 9 _·_
infix  7 _≡_

postulate
  D                      : Set
  _·_                    : D → D → D
  true false if          : D
  zero succ pred iszero  : D
  _≡_                    : D → D → Set

postulate
  if-true  : ∀ t {t'} → if · true  · t · t' ≡ t
  if-false : ∀ {t} t' → if · false · t · t' ≡ t'
  pred-0   : pred · zero ≡ zero
  pred-S   : ∀ n → pred · (succ · n) ≡ n
  iszero-0 : iszero · zero ≡ true
  iszero-S : ∀ n → iszero · (succ · n) ≡ false
{-# ATP axiom if-true if-false pred-0 pred-S iszero-0 iszero-S #-}

postulate
  +    : D
  +-eq : ∀ m n → + · m · n ≡
         if · (iszero · m) · n · (succ · (+ · (pred · m) · n))
{-# ATP axiom +-eq #-}

postulate
  +-0x : ∀ n → + · zero · n ≡ n
  +-Sx : ∀ m n → + · (succ · m) · n ≡ succ · (+ · m · n)
{-# ATP prove +-0x #-}
{-# ATP prove +-Sx #-}

-- $ cd fotc/notes/thesis
-- $ agda -i. -i ~/fot FOTC/AddConstant.agda
-- $ apia -i. -i ~/fot FOTC/AddConstant.agda
-- Proving the conjecture in /tmp/FOTC/AddConstant/37-43-0x.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture
-- Proving the conjecture in /tmp/FOTC/AddConstant/38-43-Sx.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture
