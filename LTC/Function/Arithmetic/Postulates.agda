module LTC.Function.Arithmetic.Postulates where

open import LTC.Minimal

open import LTC.Data.N
open import LTC.Function.Arithmetic

postulate
  [x-y]z≡xz*yz : {m n o : D} → N m → N n → N o → (m - n) * o ≡ m * o - n * o

postulate
  [x+y]-[x+z]≡y-z : {m n o : D} → N m → N n → N o → (m + n) - (m + o) ≡ n - o
