------------------------------------------------------------------------------
-- Properties of McCarthy 91 function
------------------------------------------------------------------------------

module Draft.McCarthy91.PropertiesATP where

open import LTC.Base

open import Draft.McCarthy91.McCarthy91
open import Draft.McCarthy91.ArithmeticATP

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesATP
open import LTC.Data.Nat.PropertiesATP
open import LTC.Data.Nat.Unary.IsN-ATP
open import LTC.Data.Nat.Unary.Numbers

------------------------------------------------------------------------------

postulate n<n+1 : ∀ {n} → N n → LT n (n + one)
{-# ATP prove n<n+1 x<Sx +-comm #-}

postulate n+1<=n-10+11 : ∀ {n} → N n →  LE (n + one) ((n ∸ ten) + eleven)
{-# ATP prove n+1<=n-10+11 x≤y+x∸y N10 1+x-N 11+x-N x∸10-N +-comm #-}


---- Case n > 100
postulate term>100     : ∀ n → N n → GT n one-hundred → N (mc91 n)
          f>100≡n-10   : ∀ n → GT n one-hundred → mc91 n ≡ n ∸ ten
          >100-n<fn+11 : ∀ n → N n → GT n one-hundred → LT n (mc91 n + eleven)
{-# ATP prove term>100 x∸10-N #-}
{-# ATP prove f>100≡n-10 #-}
{-# ATP prove >100-n<fn+11 x<y→y≤z→x<z n<n+1 n+1<=n-10+11 1+x-N 11+x-N x∸10-N
              +-comm
#-}


---- Case n ≡ 100
postulate
  term≡100     : N (mc91 one-hundred)
  f100≡91      : mc91 one-hundred ≡ ninety-one
  ≡100-n<fn+11 : LT  one-hundred (mc91 one-hundred + eleven)
{-# ATP prove term≡100 111>100 101>100 n101 n91 term>100 N111 N101 #-}
{-# ATP prove f100≡91 111>100 101>100 n101 n91 #-}
{-# ATP prove term≡100 f100≡91 111>100 101>100 n101 n91 N91 #-}
{-# ATP prove ≡100-n<fn+11 f100≡91 n102 100<102 #-}



-- $ agda -isrc -i. Draft/McCarthy91/McCarthy91.agda
-- $ agda2atp -isrc -i. --atp=e --atp=equinox Draft/McCarthy91/McCarthy91.agda
