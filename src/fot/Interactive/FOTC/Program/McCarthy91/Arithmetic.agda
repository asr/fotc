------------------------------------------------------------------------------
-- Arithmetic properties used by the McCarthy 91 function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.McCarthy91.Arithmetic where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.Properties
  using ( +-N
        ; ∸-N
        ; +-comm
        ; [x+Sy]∸y≡Sx
        )
open import Interactive.FOTC.Data.Nat.UnaryNumbers
open import Interactive.FOTC.Data.Nat.UnaryNumbers.Totality
  using ( 10-N
        ; 11-N
        )

------------------------------------------------------------------------------

-- TODO (2019-06-09): Missing proof.
postulate 91≡100+11∸10∸10 : 91' ≡ 100' + 11' ∸ 10' ∸ 10'

-- TODO (2019-06-09): Missing proofs.
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

-- TODO (2019-06-09): Missing proof.
postulate 101≡100+11∸10 : 101' ≡ 100' + 11' ∸ 10'

-- TODO (2019-06-09): Missing proofs.
postulate
  100+11∸10>100 : 100' + 11' ∸ 10' > 100'
  100+11>100    : 100' + 11'       > 100'

-- TODO (2019-06-09): Missing proofs.
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

x+11-N : ∀ {n} → N n → N (n + 11')
x+11-N Nn = +-N Nn 11-N

x+11∸10≡Sx : ∀ {n} → N n → n + 11' ∸ 10' ≡ succ₁ n
x+11∸10≡Sx Nn = [x+Sy]∸y≡Sx Nn 10-N

-- TODO (2019-06-09): Missing proofs.
postulate x+1≤x∸10+11 : ∀ {n} → N n → n + 1' ≤ (n ∸ 10') + 11'

-- TODO (2019-06-09): Missing proofs.
postulate x≤89→x+11≯100 : ∀ {n} → N n → n ≤ 89' → n + 11' ≯ 100'
