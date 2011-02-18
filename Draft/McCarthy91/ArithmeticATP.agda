------------------------------------------------------------------------------
-- Arithmetic properties used by the McCarthy 91 function
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
  102>100  : GT hundred-two one-hundred
  103>100  : GT hundred-three one-hundred
  104>100  : GT hundred-four one-hundred
  105>100  : GT hundred-five one-hundred
  106>100  : GT hundred-six one-hundred
  107>100  : GT hundred-seven one-hundred
  108>100  : GT hundred-eight one-hundred
  109>100  : GT hundred-nine one-hundred
  110>100  : GT hundred-ten one-hundred
  111>100' : GT hundred-eleven one-hundred
  111>100  : GT (one-hundred + eleven) one-hundred
{-# ATP prove 101>100' #-}
{-# ATP prove 101>100 101>100' 101≡100+11-10 #-}
{-# ATP prove 102>100 #-}
{-# ATP prove 103>100 #-}
{-# ATP prove 104>100 #-}
{-# ATP prove 105>100 #-}
{-# ATP prove 106>100 #-}
{-# ATP prove 107>100 #-}
{-# ATP prove 108>100 #-}
{-# ATP prove 109>100 #-}
{-# ATP prove 110>100 #-}
{-# ATP prove 111>100' #-}
{-# ATP prove 111>100 111>100' 111≡100+11 #-}

postulate
  99+11>100 : GT (ninety-nine + eleven) one-hundred
  98+11>100 : GT (ninety-eight + eleven) one-hundred
  97+11>100 : GT (ninety-seven + eleven) one-hundred
  96+11>100 : GT (ninety-six + eleven) one-hundred
  95+11>100 : GT (ninety-five + eleven) one-hundred
  94+11>100 : GT (ninety-four + eleven) one-hundred
  93+11>100 : GT (ninety-three + eleven) one-hundred
  92+11>100 : GT (ninety-two + eleven) one-hundred
  91+11>100 : GT (ninety-one + eleven) one-hundred
  90+11>100 : GT (ninety + eleven) one-hundred
{-# ATP prove 99+11>100 110>100 110≡99+11 #-}
{-# ATP prove 98+11>100 109>100 109≡99+11 #-}
{-# ATP prove 97+11>100 108>100 108≡97+11 #-}
{-# ATP prove 96+11>100 107>100 107≡96+11 #-}
{-# ATP prove 95+11>100 106>100 106≡95+11 #-}
{-# ATP prove 94+11>100 105>100 105≡94+11 #-}
{-# ATP prove 93+11>100 104>100 104≡93+11 #-}
{-# ATP prove 92+11>100 103>100 103≡92+1 #-}
{-# ATP prove 91+11>100 102>100 102≡91+11 #-}
{-# ATP prove 90+11>100 101>100' 101≡90+11≡101 #-}

postulate
  100<102' : LT one-hundred hundred-two
  100<102  : LT one-hundred (ninety-one + eleven)
{-# ATP prove 100<102' #-}
{-# ATP prove 100<102 100<102' 102≡91+11 #-}

x+11-N : ∀ {n} → N n → N (n + eleven)
x+11-N Nn = +-N Nn N11

x+11∸10≡Sx : ∀ {n} → N n → (n + eleven) ∸ ten ≡ succ n
x+11∸10≡Sx Nn = [x+Sy]∸y≡Sx Nn N10

postulate 91>100→⊥ : GT ninety-one one-hundred → ⊥
{-# ATP prove 91>100→⊥ #-}

postulate x+1≤x∸10+11 : ∀ {n} → N n → LE (n + one) ((n ∸ ten) + eleven)
{-# ATP prove x+1≤x∸10+11 x≤y+x∸y N10 N11 +-N +-comm #-}

postulate x≤89→x+11>100→⊥ : ∀ {n} → N n → LE n eighty-nine →
                            GT (n + eleven) one-hundred → ⊥
{-# ATP prove x≤89→x+11>100→⊥ x>y→x≤y→⊥ x≤y→x+k≤y+k x+11-N N89 N100 100≡89+11 #-}
