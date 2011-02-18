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
  91≡[100+11∸10]∸10 : (one-hundred + eleven ∸ ten) ∸ ten ≡ ninety-one
{-# ATP prove 91≡[100+11∸10]∸10 #-}

postulate
  100≡89+11     : eighty-nine + eleven         ≡ one-hundred
  101≡90+11≡101 : ninety + eleven              ≡ hundred-one
  101≡100+11-10 : (one-hundred + eleven) ∸ ten ≡ hundred-one
  102≡91+11     : ninety-one + eleven          ≡ hundred-two
  103≡92+1      : ninety-two + eleven          ≡ hundred-three
  104≡93+11     : ninety-three + eleven        ≡ hundred-four
  105≡94+11     : ninety-four + eleven         ≡ hundred-five
  106≡95+11     : ninety-five + eleven         ≡ hundred-six
  107≡96+11     : ninety-six + eleven          ≡ hundred-seven
  108≡97+11     : ninety-seven + eleven        ≡ hundred-eight
  109≡99+11     : ninety-eight + eleven        ≡ hundred-nine
  110≡99+11     : ninety-nine + eleven         ≡ hundred-ten
  111≡100+11    : one-hundred + eleven         ≡ hundred-eleven

{-# ATP prove 100≡89+11 #-}
{-# ATP prove 101≡90+11≡101 #-}
{-# ATP prove 101≡100+11-10 #-}
{-# ATP prove 102≡91+11 #-}
{-# ATP prove 103≡92+1 #-}
{-# ATP prove 104≡93+11 #-}
{-# ATP prove 105≡94+11 #-}
{-# ATP prove 106≡95+11 #-}
{-# ATP prove 107≡96+11 #-}
{-# ATP prove 108≡97+11 #-}
{-# ATP prove 109≡99+11 #-}
{-# ATP prove 110≡99+11 #-}
{-# ATP prove 111≡100+11 #-}

postulate
  101>100' : GT hundred-one one-hundred
  101>100  : GT ((one-hundred + eleven) ∸ ten) one-hundred
  111>100' : GT hundred-eleven one-hundred
  111>100  : GT (one-hundred + eleven) one-hundred
  100<102' : LT one-hundred hundred-two
  100<102  : LT one-hundred (ninety-one + eleven)
{-# ATP prove 101>100' #-}
{-# ATP prove 101>100 101>100' 101≡100+11-10 #-}
{-# ATP prove 111>100' #-}
{-# ATP prove 111>100 111>100' 111≡100+11 #-}
{-# ATP prove 100<102' #-}
{-# ATP prove 100<102 100<102' 102≡91+11 #-}

postulate 91>100→⊥ : GT ninety-one one-hundred → ⊥
{-# ATP prove 91>100→⊥ #-}

postulate x+1≤x∸10+11 : ∀ {n} → N n → LE (n + one) ((n ∸ ten) + eleven)
{-# ATP prove x+1≤x∸10+11 x≤y+x∸y N10 1+x-N 11+x-N x∸10-N +-comm #-}

postulate x≤89→x+11>100→⊥ : ∀ {n} → N n → LE n eighty-nine →
                            GT (n + eleven) one-hundred → ⊥
{-# ATP prove x≤89→x+11>100→⊥ x>y→x≤y→⊥ x≤y→x+k≤y+k x+11-N N89 N100 100≡89+11 #-}
