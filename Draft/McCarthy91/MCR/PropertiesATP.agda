------------------------------------------------------------------------------
-- Properties for the MCR relation
------------------------------------------------------------------------------

module Draft.McCarthy91.MCR.PropertiesATP where

open import LTC.Base

open import Draft.McCarthy91.ArithmeticATP
open import Draft.McCarthy91.MCR

open import LTC.Data.Nat
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesATP
open import LTC.Data.Nat.PropertiesATP
open import LTC.Data.Nat.Unary.Numbers
open import LTC.Data.Nat.Unary.IsN-ATP

------------------------------------------------------------------------------

0«x→⊥ : ∀ {n} → N n → ¬ (MCR zero n)
0«x→⊥ zN 0«n = prf
  where
    postulate prf : ⊥
    {-# ATP prove prf #-}

0«x→⊥ (sN Nn) 0«Sn = prf
  where
    postulate prf : ⊥
    {-# ATP prove prf ∸-N x∸y<Sx x<y→y<x→⊥ #-}

«-trans : ∀ {m n o} → N m → N n → N o → MCR m n → MCR n o → MCR m o
«-trans Nm Nn No m«n n«o =
  <-trans (∸-N N101 Nm) (∸-N N101 Nn) (∸-N N101 No) m«n n«o

Sx«Sy→x«y : ∀ {m n} → N m → N n → MCR (succ m) (succ n) → MCR m n
Sx«Sy→x«y zN zN S0«S0 = prf
  where
    postulate prf : MCR zero zero
    {-# ATP prove prf #-}

Sx«Sy→x«y zN (sN {n} Nn) S0«SSn = prf
  where
    postulate prf : MCR zero (succ n)
    {-# ATP prove prf x<x∸y→⊥ #-}

Sx«Sy→x«y (sN {m} Nm) zN SSm«S0 = prf
  where
    postulate prf : MCR (succ m) zero
    {-# ATP prove prf ∸-N x∸y<Sx #-}

Sx«Sy→x«y (sN {m} Nm) (sN {n} Nn) SSm«SSn = prf
  where
    postulate prf : MCR (succ m) (succ n)
    {-# ATP prove prf x∸y<x∸z→Sx∸y<Sx∸z #-}

x«Sy→x«y : ∀ {m n} → N m → N n → MCR m (succ n) → MCR m n
x«Sy→x«y {n = n} zN Nn 0«Sn = ⊥-elim (0«x→⊥ (sN Nn) 0«Sn)

x«Sy→x«y (sN {m} Nm) zN Sm«S0 = prf
   where
     postulate prf : MCR (succ m) zero
     {-# ATP prove prf x∸y<Sx #-}

x«Sy→x«y (sN {m} Nm) (sN {n} Nn) Sm«SSn =
  x<y→y≤z→x<z (∸-N N101 (sN Nm))
              (∸-N N101 (sN (sN Nn)))
              (∸-N N101 (sN Nn))
              Sm«SSn
              (x∸Sy≤x∸y N101 (sN Nn))
