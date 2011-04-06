------------------------------------------------------------------------------
-- Property LT2MCR which proves that the recursive calls of the
-- McCarthy 91 function are on smaller arguments.
------------------------------------------------------------------------------

module FOTC.Program.McCarthy91.MCR.LT2MCR-ATP where

open import FOTC.Base

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.IsN-ATP

open import FOTC.Program.McCarthy91.MCR

------------------------------------------------------------------------------

LT2MCR-helper : ∀ {n m k} → N n → N m → N k →
                LT m n → LT (succ n) k → LT (succ m) k →
                LT (k ∸ n) (k ∸ m) → LT (k ∸ succ n) (k ∸ succ m)
LT2MCR-helper zN Nm Nk p qn qm h = ⊥-elim (x<0→⊥ Nm p)
LT2MCR-helper (sN Nn) Nm zN p qn qm h = ⊥-elim (x<0→⊥ (sN Nm) qm)
LT2MCR-helper (sN {n} Nn) zN (sN {k} Nk) p qn qm h = prfS0S
  where
    postulate k≥Sn   : GE k (succ n)
              k∸Sn<k : LT (k ∸ (succ n)) k
              prfS0S : LT (succ k ∸ succ (succ n)) (succ k ∸ succ zero)
    {-# ATP prove k≥Sn x<y→x≤y #-}
    {-# ATP prove k∸Sn<k k≥Sn x≥y→y>0→x∸y<x #-}
    {-# ATP prove prfS0S k∸Sn<k #-}

LT2MCR-helper (sN {n} Nn) (sN {m} Nm) (sN {k} Nk) p qn qm h =
  k∸Sn<k∸Sm→Sk∸SSn<Sk∸SSm (LT2MCR-helper Nn Nm Nk m<n Sn<k Sm<k k∸n<k∸m)
  where
    postulate
      k∸Sn<k∸Sm→Sk∸SSn<Sk∸SSm : LT (k ∸ succ n) (k ∸ succ m) →
                                LT (succ k ∸ succ (succ n))
                                   (succ k ∸ succ (succ m))
    {-# ATP prove  k∸Sn<k∸Sm→Sk∸SSn<Sk∸SSm #-}

    postulate
      m<n     : LT m n
      Sn<k    : LT (succ n) k
      Sm<k    : LT (succ m) k
      k∸n<k∸m : LT (k ∸ n) (k ∸ m)
    {-# ATP prove m<n #-}
    {-# ATP prove Sn<k #-}
    {-# ATP prove Sm<k #-}
    {-# ATP prove k∸n<k∸m #-}

LT2MCR : ∀ {n m} → N n → N m → LE m one-hundred → LT m n → MCR n m
LT2MCR zN Nm p h = ⊥-elim (x<0→⊥ Nm h)
LT2MCR (sN {n} Nn) zN p h = prfS0
  where
    postulate prfS0 : MCR (succ n) zero
    {-# ATP prove prfS0 x∸y<Sx #-}

LT2MCR (sN {n} Nn) (sN {m} Nm) p h with x<y∨x≥y Nn 100-N
... | inj₁ n<100 = LT2MCR-helper Nn Nm 101-N m<n Sn≤101 Sm≤101
                                 (LT2MCR Nn Nm m≤100 m<n)
  where
    postulate m≤100  : LE m one-hundred
              m<n    : LT m n
              Sn≤101 : LT (succ n) hundred-one
              Sm≤101 : LT (succ m) hundred-one
    {-# ATP prove m≤100 x<y→x≤y #-}
    {-# ATP prove m<n #-}
    {-# ATP prove Sn≤101 #-}
    {-# ATP prove Sm≤101 #-}
... | inj₂ n≥100 = prf-n≥100
  where
    postulate
      101∸Sn≡0  : hundred-one ∸ succ n ≡ zero
      0<101∸Sm  : LT zero (hundred-one ∸ succ m)
      prf-n≥100 : MCR (succ n) (succ m)
    {-# ATP prove 101∸Sn≡0 x≤y→x-y≡0 #-}
    {-# ATP prove 0<101∸Sm x<y→0<x∸y #-}
    {-# ATP prove prf-n≥100 101∸Sn≡0 0<101∸Sm #-}
