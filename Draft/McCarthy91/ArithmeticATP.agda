------------------------------------------------------------------------------
-- Arithmetic stuff used by the McCarthy 91 function
------------------------------------------------------------------------------

module Draft.McCarthy91.ArithmeticATP where

open import LTC.Base

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.PropertiesATP
open import LTC.Data.Nat.Unary.Numbers

------------------------------------------------------------------------------

postulate
  N0   : N zero
  N1   : N one
  N10  : N ten
  N91  : N ninety-one
  N100 : N one-hundred
  N101 : N hundred-one
  N111 : N hundred-eleven
{-# ATP prove N0 #-}
{-# ATP prove N1 #-}
{-# ATP prove N10 #-}
{-# ATP prove N91 #-}
{-# ATP prove N100 #-}
{-# ATP prove N101 #-}
{-# ATP prove N111 #-}


postulate
  N1+n  : ∀ {n} → N n → N (one + n)
  N11+n : ∀ {n} → N n → N (eleven + n)
  Nn-10 : ∀ {n} → N n → N (n ∸ ten)
{-# ATP prove N1+n #-}
{-# ATP prove N11+n #-}
{-# ATP prove Nn-10 ∸-N N10 #-}


postulate
  n111' : eleven + one-hundred ≡ hundred-eleven
  n111  : one-hundred + eleven ≡ hundred-eleven
  n101' : hundred-eleven ∸ ten ≡ hundred-one
  n101  : (one-hundred + eleven) ∸ ten ≡ hundred-one
  n91'  : hundred-one ∸ ten ≡ ninety-one
  n91   : ((one-hundred + eleven) ∸ ten) ∸ ten ≡ ninety-one
  n102' : eleven + ninety-one ≡ hundred-two
  n102  : ninety-one + eleven ≡ hundred-two
{-# ATP prove n111' #-}
{-# ATP prove n111 +-comm n111' #-}
{-# ATP prove n101' #-}
{-# ATP prove n101 n111 n101' #-}
{-# ATP prove n91' #-}
{-# ATP prove n91 n101 n91' #-}
{-# ATP prove n102' #-}
{-# ATP prove n102 n102' +-comm #-}


postulate
  101>100' : GT hundred-one one-hundred
  101>100  : GT ((one-hundred + eleven) ∸ ten) one-hundred
  111>100' : GT hundred-eleven one-hundred
  111>100  : GT (one-hundred + eleven) one-hundred
  100<102' : LT one-hundred hundred-two
  100<102  : LT one-hundred (ninety-one + eleven)
{-# ATP prove 101>100' #-}
{-# ATP prove 101>100 101>100' n101 #-}
{-# ATP prove 111>100' #-}
{-# ATP prove 111>100 111>100' n111 #-}
{-# ATP prove 100<102' #-}
{-# ATP prove 100<102 100<102' n102 #-}
