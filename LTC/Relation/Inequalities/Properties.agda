------------------------------------------------------------------------------
-- Properties of the inequalities
------------------------------------------------------------------------------

module LTC.Relation.Inequalities.Properties where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.Properties
open import LTC.Relation.Inequalities

open import MyStdLib.Data.Sum
open import MyStdLib.Function

------------------------------------------------------------------------------

-- TODO: Why the ATP couldn't prove it?
-- postulate
--   x≥0 : (n : D) → N n → GE n zero
-- {-# ATP prove x≥0 zN sN #-}

x≥0 : {n : D} → N n → GE n zero
x≥0 zN          = lt-00
x≥0 (sN {n} Nn) = lt-S0 n
-- {-# ATP hint x≥0 #-}

¬x<0 : {n : D} → N n → ¬ (LT n zero)
¬x<0 zN 0<0 = ⊥-elim prf
  where
  postulate prf : ⊥
  {-# ATP prove prf #-}
¬x<0 (sN Nn) Sn<0 = ⊥-elim prf
  where
  postulate prf : ⊥
  {-# ATP prove prf #-}

¬0>x : {n : D} → N n → ¬ (GT zero n)
¬0>x Nn 0>n = ⊥-elim prf
  where
    postulate
      prf : ⊥
    {-# ATP prove prf x≥0 #-}

¬S≤0 : {d : D} → ¬ (LE (succ d) zero)
¬S≤0 Sd≤0 = ⊥-elim prf
  where
    postulate
      -- The proof uses the axiom true≠false
      prf : ⊥
    {-# ATP prove prf #-}

x<Sx : {n : D} → N n → LT n (succ n)
x<Sx zN          = lt-0S zero
x<Sx (sN {n} Nn) = prf (x<Sx Nn)
  where
  postulate prf : LT n (succ n) → LT (succ n) (succ (succ n))
  {-# ATP prove prf #-}

x>y∨x≤y : {m n : D} → N m → N n → GT m n ∨ LE m n
x>y∨x≤y zN          Nn          = inj₂ $ x≥0 Nn
x>y∨x≤y (sN {m} Nm) zN          = inj₁ $ lt-0S m
x>y∨x≤y (sN {m} Nm) (sN {n} Nn) = prf $ x>y∨x≤y Nm Nn
  where
    postulate
      prf : (GT m n) ∨ (LE m n) →
            GT (succ m) (succ n) ∨ LE (succ m) (succ n)
    {-# ATP prove prf #-}

¬x<x : {m : D} → N m → ¬ (LT m m)
¬x<x zN _ = ⊥-elim prf
  where
  postulate prf : ⊥
  {-# ATP prove prf #-}
¬x<x (sN {m} Nm) _ = ⊥-elim (prf (¬x<x Nm))
  where
  postulate prf : ¬ (LT m m) → ⊥
  {-# ATP prove prf #-}

trans-LT : {m n o : D} → N m → N n → N o → LT m n → LT n o → LT m o
trans-LT zN          zN           _          0<0   _    = ⊥-elim (¬x<0 zN 0<0)
trans-LT zN          (sN Nn)     zN          _     Sn<0 = ⊥-elim (¬x<0 (sN Nn) Sn<0)
trans-LT zN          (sN Nn)     (sN {o} No) _     _    = lt-0S o
trans-LT (sN Nm)     Nn          zN          _     n<0  = ⊥-elim (¬x<0 Nn n<0)
trans-LT (sN Nm)     zN          (sN No)     Sm<0  _    = ⊥-elim (¬x<0 (sN Nm) Sm<0)
trans-LT (sN {m} Nm) (sN {n} Nn) (sN {o} No) Sm<Sn Sn<So =
  prf (trans-LT Nm Nn No m<n n<o)

  where
  postulate prf : lt m o ≡ true →
                  lt (succ m) (succ o) ≡ true
  {-# ATP prove prf #-}

  postulate m<n : lt m n ≡ true
  {-# ATP prove m<n #-}

  postulate n<o : lt n o ≡ true
  {-# ATP prove n<o #-}

x≤x+y : {m n : D} → N m → N n → LE m (m + n)
x≤x+y         zN          Nn = x≥0 (+-N zN Nn)
x≤x+y {n = n} (sN {m} Nm) Nn = prf (x≤x+y Nm Nn)
  where
  postulate prf : lt (m + n) m ≡ false →
                  lt (succ m + n) (succ m) ≡ false
  {-# ATP prove prf #-}

x-y<Sx : {m n : D} → N m → N n → LT (m - n) (succ m)
x-y<Sx {m} Nm zN = prf
  where
  postulate prf : lt (m - zero) (succ m) ≡ true
  {-# ATP prove prf x<Sx #-}

x-y<Sx zN (sN {n} Nn) = prf
  where
  postulate prf : lt (zero - succ n) (succ zero) ≡ true
  {-# ATP prove prf #-}

x-y<Sx (sN {m} Nm) (sN {n} Nn) = prf (x-y<Sx Nm Nn)
  where
  postulate prf : lt (m - n) (succ m) ≡ true →
                  lt (succ m - succ n) (succ (succ m)) ≡ true
  {-# ATP prove prf trans-LT minus-N x<Sx sN #-}

x>y→x-y+y≡x : {m n : D} → N m → N n → GT m n → (m - n) + n ≡ m
x>y→x-y+y≡x zN Nn 0>n = ⊥-elim (¬0>x Nn 0>n)
x>y→x-y+y≡x (sN {m} Nm) zN Sm>0 = prf
  where
  postulate prf : (succ m - zero) + zero ≡ succ m
  {-# ATP prove prf +-rightIdentity minus-N #-}

x>y→x-y+y≡x (sN {m} Nm) (sN {n} Nn) Sm>Sn = prf (x>y→x-y+y≡x Nm Nn m>n )
  where
  postulate m>n : GT m n
  {-# ATP prove m>n #-}

  postulate prf : (m - n) + n ≡ m →
                  (succ m - succ n) + succ n ≡ succ m
  {-# ATP prove prf +-comm minus-N sN #-}

x≤y→y-x+x≡y : {m n : D} → N m → N n → LE m n → (n - m) + m ≡ n
x≤y→y-x+x≡y {n = n} zN Nn 0≤n  = prf
  where
  postulate prf : (n - zero) + zero ≡ n
  {-# ATP prove prf +-rightIdentity minus-N #-}

x≤y→y-x+x≡y (sN Nm) zN Sm≤0 = ⊥-elim (¬S≤0 Sm≤0)

x≤y→y-x+x≡y (sN {m} Nm) (sN {n} Nn) Sm≤Sn = prf (x≤y→y-x+x≡y Nm Nn m≤n )
  where
  postulate m≤n : LE m n
  {-# ATP prove m≤n #-}

  postulate prf : (n - m) + m ≡ n →
                  (succ n - succ m) + succ m ≡ succ n
  {-# ATP prove prf +-comm minus-N sN #-}

[Sx-Sy,Sy]<[Sx,Sy] :
  {m n : D} → N m → N n →
  LT₂ (succ m - succ n) (succ n) (succ m) (succ n)
[Sx-Sy,Sy]<[Sx,Sy] {m} {n} Nm Nn = prf
  where
  postulate prf : LT₂ (succ m - succ n) (succ n) (succ m) (succ n)
  {-# ATP prove prf sN x-y<Sx #-}

[Sx,Sy-Sx]<[Sx,Sy] : {m n : D} → N m → N n →
                     LT₂ (succ m) (succ n - succ m) (succ m) (succ n)
[Sx,Sy-Sx]<[Sx,Sy] {m} {n} Nm Nn = prf
  where
  postulate prf : LT₂ (succ m) (succ n - succ m) (succ m) (succ n)
  {-# ATP prove prf sN x-y<Sx #-}

