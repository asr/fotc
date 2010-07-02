------------------------------------------------------------------------------
-- The booleans
------------------------------------------------------------------------------

module LTC.Data.Bool where

open import LTC.Minimal

------------------------------------------------------------------------------

infixr 6 _&&_

-- Basic functions.

-- The conjunction.
postulate
  _&&_  : D → D → D
  &&-tt : true  && true  ≡ true
  &&-tf : true  && false ≡ false
  &&-ft : false && true  ≡ false
  &&-ff : false && false ≡ false
{-# ATP axiom &&-tt #-}
{-# ATP axiom &&-tf #-}
{-# ATP axiom &&-ft #-}
{-# ATP axiom &&-ff #-}

------------------------------------------------------------------------------

-- The LTC booleans type.
data Bool : D → Set where
  tB : Bool true
  fB : Bool false

-- The rule of proof by case analysis on 'B'.
indBool : (P : D → Set) → P true → P false → {b : D} → Bool b → P b
indBool P pt pf tB = pt
indBool P pt pf fB = pf
