------------------------------------------------------------------------------
-- Arithmetic properties used by the McCarthy 91 function
------------------------------------------------------------------------------

module FOTC.Program.McCarthy91.ArithmeticATP where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP

------------------------------------------------------------------------------

postulate 91≡100+11∸10∸10 : ninety-one ≡ one-hundred + eleven ∸ ten ∸ ten
{-# ATP prove 91≡100+11∸10∸10 #-}

postulate
  100≡89+11     : one-hundred    ≡ eighty-nine + eleven
  101≡90+11     : hundred-one    ≡ ninety + eleven
  101≡100+11∸10 : hundred-one    ≡ one-hundred + eleven ∸ ten
  102≡91+11     : hundred-two    ≡ ninety-one + eleven
  103≡92+1      : hundred-three  ≡ ninety-two + eleven
  104≡93+11     : hundred-four   ≡ ninety-three + eleven
  105≡94+11     : hundred-five   ≡ ninety-four + eleven
  106≡95+11     : hundred-six    ≡ ninety-five + eleven
  107≡96+11     : hundred-seven  ≡ ninety-six + eleven
  108≡97+11     : hundred-eight  ≡ ninety-seven + eleven
  109≡99+11     : hundred-nine   ≡ ninety-eight + eleven
  110≡99+11     : hundred-ten    ≡ ninety-nine + eleven
  111≡100+11    : hundred-eleven ≡ one-hundred + eleven
{-# ATP prove 100≡89+11 #-}
{-# ATP prove 101≡90+11 #-}
{-# ATP prove 101≡100+11∸10 #-}
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
  100+11∸10>100 : GT (one-hundred + eleven ∸ ten) one-hundred
  100+11>100    : GT (one-hundred + eleven)       one-hundred
{-# ATP prove 100+11∸10>100 101≡100+11∸10 #-}
{-# ATP prove 100+11>100 111≡100+11 #-}

postulate
  99+11>100 : GT (ninety-nine + eleven)  one-hundred
  98+11>100 : GT (ninety-eight + eleven) one-hundred
  97+11>100 : GT (ninety-seven + eleven) one-hundred
  96+11>100 : GT (ninety-six + eleven)   one-hundred
  95+11>100 : GT (ninety-five + eleven)  one-hundred
  94+11>100 : GT (ninety-four + eleven)  one-hundred
  93+11>100 : GT (ninety-three + eleven) one-hundred
  92+11>100 : GT (ninety-two + eleven)   one-hundred
  91+11>100 : GT (ninety-one + eleven)   one-hundred
  90+11>100 : GT (ninety + eleven)       one-hundred
{-# ATP prove 99+11>100 110≡99+11 #-}
{-# ATP prove 98+11>100 109≡99+11 #-}
{-# ATP prove 97+11>100 108≡97+11 #-}
{-# ATP prove 96+11>100 107≡96+11 #-}
{-# ATP prove 95+11>100 106≡95+11 #-}
{-# ATP prove 94+11>100 105≡94+11 #-}
{-# ATP prove 93+11>100 104≡93+11 #-}
{-# ATP prove 92+11>100 103≡92+1 #-}
{-# ATP prove 91+11>100 102≡91+11 #-}
{-# ATP prove 90+11>100 101≡90+11 #-}

postulate 100<102 : LT one-hundred hundred-two
{-# ATP prove 100<102 #-}

x+11-N : ∀ {n} → N n → N (n + eleven)
x+11-N Nn = +-N Nn 11-N

x+11∸10≡Sx : ∀ {n} → N n → (n + eleven) ∸ ten ≡ succ n
x+11∸10≡Sx Nn = [x+Sy]∸y≡Sx Nn 10-N

postulate 91>100→⊥ : GT ninety-one one-hundred → ⊥
{-# ATP prove 91>100→⊥ #-}

postulate x+1≤x∸10+11 : ∀ {n} → N n → LE (n + one) ((n ∸ ten) + eleven)
{-# ATP prove x+1≤x∸10+11 x≤y+x∸y 10-N 11-N +-N ∸-N +-comm #-}

postulate
  x≤89→x+11>100→⊥ : ∀ {n} → N n → LE n eighty-nine →
                    GT (n + eleven) one-hundred → ⊥
{-# ATP prove x≤89→x+11>100→⊥ x>y→x≤y→⊥ x≤y→x+k≤y+k x+11-N 89-N 100-N
                              100≡89+11
#-}
