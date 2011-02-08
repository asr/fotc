module Draft.McCarthy91.Arithmetic where

open import LTC.Base

open import Draft.McCarthy91.Numbers
open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities

postulate
  1+1>1 : GT (one + one) one
{-# ATP prove 1+1>1 #-}

postulate
  10+90≡100 : ten + ninety ≡ one-hundred
{-# ATP prove 10+90≡100 #-}

postulate
  90+10≡100 : ninety + ten ≡ one-hundred
{-# ATP prove 90+10≡100 #-}

postulate
  100-10≡90 : one-hundred ∸ ten ≡ ninety
{-# ATP prove 100-10≡90 #-}
