module LTC.Relation.Inequalities.Postulates where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Function.Arithmetic
open import LTC.Relation.Inequalities

------------------------------------------------------------------------------

postulate
  Sx>Sy→[Sx-Sy,Sy]<₂[Sx,Sy] :
    {m n : D} → N m → N n →
    GT (succ m) (succ n) →
    LT₂ ( succ m - succ n , succ n ) ( succ m , succ n )

postulate
  Sx≤Sy→[Sx,Sy-Sx]<₂[Sx,Sy] : {m n : D} → N m → N n → LE (succ m) (succ n) →
                              LT₂ (succ m , succ n - succ m) (succ m , succ n)

postulate
  x>y→x-y+y≡x : {m n : D} → N m → N n → GT m n → (m - n) + n ≡ m

postulate
  x≤y→y-x+x≡y : {m n : D} → N m → N n → LE m n → (n - m) + m ≡ n

