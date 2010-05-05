module Postulates where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Function.Arithmetic
open import LTC.Relation.Inequalities

open import MyStdLib.Induction.WellFounded
import MyStdLib.Induction.Lexicographic
open module PostulatesLT₂ = MyStdLib.Induction.Lexicographic LT LT

postulate
  wellFoundedLT : WellFounded LT

postulate
  Sx>Sy→[Sx-Sy,Sy]<[Sx,Sy] :
    {m n : D} → N m → N n →
    GT (succ m) (succ n) →
    LT₂ ( succ m - succ n , succ n ) ( succ m , succ n )

postulate
  Sx≤Sy→[Sx,Sy-Sx]<[Sx,Sy] : {m n : D} → N m → N n → LE (succ m) (succ n) →
                             LT₂ (succ m , succ n - succ m) (succ m , succ n)

postulate
  x>y→x-y+y≡x : {m n : D} → N m → N n → GT m n → (m - n) + n ≡ m

postulate
  x≤y→y-x+x≡y : {m n : D} → N m → N n → LE m n → (n - m) + m ≡ n
