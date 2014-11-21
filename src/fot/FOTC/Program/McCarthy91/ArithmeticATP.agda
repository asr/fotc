------------------------------------------------------------------------------
-- Arithmetic properties used by the McCarthy 91 function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.McCarthy91.ArithmeticATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
  using ( x≤y+x∸y
        ; x≤y→x≯y
        ; x≤y→x+k≤y+k
        )
open import FOTC.Data.Nat.PropertiesATP
  using ( +-N
        ; ∸-N
        ; +-comm
        ; [x+Sy]∸y≡Sx
        )
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP
  using ( 10-N
        ; 11-N
        ; 89-N
        ; 100-N
        )

------------------------------------------------------------------------------

postulate 91≡100+11∸10∸10 : 91' ≡ 100' + 11' ∸ 10' ∸ 10'
{-# ATP prove 91≡100+11∸10∸10 #-}

postulate
  100≡89+11  : 100' ≡ 89' + 11'
  101≡90+11  : 101' ≡ 90' + 11'
  102≡91+11  : 102' ≡ 91' + 11'
  103≡92+11  : 103' ≡ 92' + 11'
  104≡93+11  : 104' ≡ 93' + 11'
  105≡94+11  : 105' ≡ 94' + 11'
  106≡95+11  : 106' ≡ 95' + 11'
  107≡96+11  : 107' ≡ 96' + 11'
  108≡97+11  : 108' ≡ 97' + 11'
  109≡98+11  : 109' ≡ 98' + 11'
  110≡99+11  : 110' ≡ 99' + 11'
  111≡100+11 : 111' ≡ 100' + 11'
{-# ATP prove 100≡89+11 #-}
{-# ATP prove 101≡90+11 #-}
{-# ATP prove 102≡91+11 #-}
{-# ATP prove 103≡92+11 #-}
{-# ATP prove 104≡93+11 #-}
{-# ATP prove 105≡94+11 #-}
{-# ATP prove 106≡95+11 #-}
{-# ATP prove 107≡96+11 #-}
{-# ATP prove 108≡97+11 #-}
{-# ATP prove 109≡98+11 #-}
{-# ATP prove 110≡99+11 #-}
{-# ATP prove 111≡100+11 #-}

postulate 101≡100+11∸10 : 101' ≡ 100' + 11' ∸ 10'
{-# ATP prove 101≡100+11∸10 #-}

postulate
  100+11∸10>100 : 100' + 11' ∸ 10' > 100'
  100+11>100    : 100' + 11'       > 100'
{-# ATP prove 100+11∸10>100 101≡100+11∸10 #-}
{-# ATP prove 100+11>100 111≡100+11 #-}

postulate
  99+11>100 : 99' + 11' > 100'
  98+11>100 : 98' + 11' > 100'
  97+11>100 : 97' + 11' > 100'
  96+11>100 : 96' + 11' > 100'
  95+11>100 : 95' + 11' > 100'
  94+11>100 : 94' + 11' > 100'
  93+11>100 : 93' + 11' > 100'
  92+11>100 : 92' + 11' > 100'
  91+11>100 : 91' + 11' > 100'
  90+11>100 : 90' + 11' > 100'
{-# ATP prove 99+11>100 110≡99+11 #-}
{-# ATP prove 98+11>100 109≡98+11 #-}
{-# ATP prove 97+11>100 108≡97+11 #-}
{-# ATP prove 96+11>100 107≡96+11 #-}
{-# ATP prove 95+11>100 106≡95+11 #-}
{-# ATP prove 94+11>100 105≡94+11 #-}
{-# ATP prove 93+11>100 104≡93+11 #-}
{-# ATP prove 92+11>100 103≡92+11 #-}
{-# ATP prove 91+11>100 102≡91+11 #-}
{-# ATP prove 90+11>100 101≡90+11 #-}

x+11-N : ∀ {n} → N n → N (n + 11')
x+11-N Nn = +-N Nn 11-N

x+11∸10≡Sx : ∀ {n} → N n → n + 11' ∸ 10' ≡ succ₁ n
x+11∸10≡Sx Nn = [x+Sy]∸y≡Sx Nn 10-N

postulate x+1≤x∸10+11 : ∀ {n} → N n → n + 1' ≤ (n ∸ 10') + 11'
{-# ATP prove x+1≤x∸10+11 x≤y+x∸y 10-N 11-N +-N ∸-N +-comm #-}

postulate x≤89→x+11≯100 : ∀ {n} → N n → n ≤ 89' → n + 11' ≯ 100'
{-# ATP prove x≤89→x+11≯100 x≤y→x≯y x≤y→x+k≤y+k x+11-N 89-N 100-N 100≡89+11 #-}
