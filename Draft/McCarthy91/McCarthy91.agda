------------------------------------------------------------------------------
-- McCarthy 91 function
------------------------------------------------------------------------------

module Draft.McCarthy91.McCarthy91 where

open import LTC.Base

open import Draft.McCarthy91.Arithmetic

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesATP
open import LTC.Data.Nat.Numbers
open import LTC.Data.Nat.PropertiesATP

------------------------------------------------------------------------------

-- McCarthy 91 function
postulate
  mc91     : D → D
  mc91-eq₁ : ∀ n → GT n one-hundred → mc91 n ≡ n ∸ ten
  mc91-eq₂ : ∀ n → LE n one-hundred → mc91 n ≡ mc91 (mc91 (n + eleven))
{-# ATP axiom mc91-eq₁ #-}
{-# ATP axiom mc91-eq₂ #-}


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
