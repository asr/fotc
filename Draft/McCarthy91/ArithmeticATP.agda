------------------------------------------------------------------------------
-- Arithmetic stuff used by the McCarthy 91 function
------------------------------------------------------------------------------

module Draft.McCarthy91.ArithmeticATP where

open import LTC.Base

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesATP
open import LTC.Data.Nat.PropertiesATP
open import LTC.Data.Nat.Unary.Numbers
open import LTC.Data.Nat.Unary.IsN-ATP

------------------------------------------------------------------------------

postulate
  1+x-N  : ∀ {n} → N n → N (one + n)
  11+x-N : ∀ {n} → N n → N (eleven + n)
  x∸10-N : ∀ {n} → N n → N (n ∸ ten)
  x+11-N : ∀ {n} → N n → N (n + eleven)
{-# ATP prove 1+x-N #-}
{-# ATP prove 11+x-N #-}
{-# ATP prove x∸10-N ∸-N N10 #-}
{-# ATP prove x+11-N 11+x-N +-comm #-}

postulate
  n111' : eleven + one-hundred ≡ hundred-eleven
  n111  : one-hundred + eleven ≡ hundred-eleven
  n101' : hundred-eleven ∸ ten ≡ hundred-one
  n101  : (one-hundred + eleven) ∸ ten ≡ hundred-one
  n91'  : hundred-one ∸ ten ≡ ninety-one
  n91   : ((one-hundred + eleven) ∸ ten) ∸ ten ≡ ninety-one
  n102' : eleven + ninety-one ≡ hundred-two
  n102  : ninety-one + eleven ≡ hundred-two
  n100' : eleven + eighty-nine ≡ one-hundred
  n100  : eighty-nine + eleven ≡ one-hundred
{-# ATP prove n111' #-}
{-# ATP prove n111 +-comm n111' #-}
{-# ATP prove n101' #-}
{-# ATP prove n101 n111 n101' #-}
{-# ATP prove n91' #-}
{-# ATP prove n91 n101 n91' #-}
{-# ATP prove n102' #-}
{-# ATP prove n102 n102' +-comm #-}
{-# ATP prove n100' #-}
{-# ATP prove n100 n100' +-comm #-}

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

postulate 91>100→⊥ : GT ninety-one one-hundred → ⊥
{-# ATP prove 91>100→⊥ #-}

postulate x+1≤x∸10+11 : ∀ {n} → N n → LE (n + one) ((n ∸ ten) + eleven)
{-# ATP prove x+1≤x∸10+11 x≤y+x∸y N10 1+x-N 11+x-N x∸10-N +-comm #-}

postulate x≤89→x+11>100→⊥ : ∀ {n} → N n → LE n eighty-nine →
                            GT (n + eleven) one-hundred → ⊥
{-# ATP prove x≤89→x+11>100→⊥ x>y→x≤y→⊥ x≤y→x+k≤y+k x+11-N N89 N100 n100 #-}
