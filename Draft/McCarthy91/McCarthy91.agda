------------------------------------------------------------------------------
-- McCarthy 91 function
------------------------------------------------------------------------------

module Draft.McCarthy91.McCarthy91 where

open import Draft.McCarthy91.Numbers

open import LTC.Base

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Type
open import LTC.Data.Nat.PropertiesATP
open import LTC.Data.Nat.Inequalities.PropertiesATP

------------------------------------------------------------------------------

-- McCarthy 91 function
postulate
  mc91     : D → D
  mc91-eq₁ : ∀ n → GT n one-hundred → mc91 n ≡ n ∸ ten
  mc91-eq₂ : ∀ n → LE n one-hundred → mc91 n ≡ mc91 (mc91 (n + eleven))
{-# ATP axiom mc91-eq₁ #-}
{-# ATP axiom mc91-eq₂ #-}

postulate N0   : N zero
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

postulate n111' : eleven + one-hundred ≡ hundred-eleven
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

postulate 101>100' : GT hundred-one one-hundred
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

postulate N1+n  : ∀ {n} → N n → N (one + n)
          N11+n : ∀ {n} → N n → N (eleven + n)
          Nn-10 : ∀ {n} → N n → N (n ∸ ten)
{-# ATP prove N1+n #-}
{-# ATP prove N11+n #-}
{-# ATP prove Nn-10 ∸-N N10 #-}

postulate n<n+1 : ∀ {n} → N n → LT n (n + one)
{-# ATP prove n<n+1 x<Sx +-comm #-}

n<=m+n-m : ∀ {n m} → N n → N m → LE n (m + (n ∸ m))
n<=m+n-m {m = m} zN Nm = prf0
  where postulate prf0 : LE zero (m + (zero ∸ m))
        {-# ATP prove prf0 0≤x +-N  #-}
n<=m+n-m (sN {n} Nn) zN = prfx0
  where postulate prfx0 : LE (succ n) (zero + (succ n ∸ zero))
        {-# ATP prove prfx0 x<Sx #-}
n<=m+n-m (sN {n} Nn) (sN {m} Nm) = prfSS (n<=m+n-m Nn Nm)
  where postulate prfSS : LE n (m + (n ∸ m)) →
                        LE (succ n) (succ m + (succ n ∸ succ m))
        {-# ATP prove prfSS x≤y→Sx≤Sy ≤-trans +-N ∸-N #-}

postulate n+1<=n-10+11 : ∀ {n} → N n →  LE (n + one) ((n ∸ ten) + eleven)
{-# ATP prove n+1<=n-10+11 n<=m+n-m N10 N1+n N11+n Nn-10 +-comm #-}

---- Case n > 100
postulate term>100     : ∀ n → N n → GT n one-hundred → N (mc91 n)
          f>100≡n-10   : ∀ n → GT n one-hundred → mc91 n ≡ n ∸ ten
          >100-n<fn+11 : ∀ n → N n → GT n one-hundred → LT n (mc91 n + eleven)
{-# ATP prove term>100 Nn-10 #-}
{-# ATP prove f>100≡n-10 #-}
{-# ATP prove >100-n<fn+11 x<y→y≤z→x<z n<n+1 n+1<=n-10+11 N1+n N11+n Nn-10
              +-comm
#-}

---- Case n ≡ 100
postulate term≡100     : N (mc91 one-hundred)
          f100≡91      : mc91 one-hundred ≡ ninety-one
          ≡100-n<fn+11 : LT  one-hundred (mc91 one-hundred + eleven)
{-# ATP prove term≡100 111>100 101>100 n101 n91 term>100 N111 N101 #-}
{-# ATP prove f100≡91 111>100 101>100 n101 n91 #-}
{-# ATP prove term≡100 f100≡91 111>100 101>100 n101 n91 N91 #-}
{-# ATP prove ≡100-n<fn+11 f100≡91 n102 100<102 #-}

-- $ agda -isrc -i. Draft/McCarthy91/McCarthy91.agda
-- $ agda2atp -isrc -i. --atp=e --atp=equinox Draft/McCarthy91/McCarthy91.agda
