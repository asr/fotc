------------------------------------------------------------------------------
-- Arithmetic properties using equational reasoning
------------------------------------------------------------------------------

module LTC.Function.Arithmetic.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER

open import LTC.Data.N
open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.Properties
  using ( +-leftIdentity ; *-leftZero  )

open import MyStdLib.Function
import MyStdLib.Relation.Binary.EqReasoning
open module APER = MyStdLib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

------------------------------------------------------------------------------
-- Closure properties

pred-N : {n : D} → N n → N (pred n)
pred-N zN          = subst (λ t → N t) (sym cP₁) zN
pred-N (sN {n} Nn) = subst (λ t → N t) (sym (cP₂ n)) Nn

minus-N : {m n : D} → N m → N n → N (m - n)
minus-N {m} Nm zN = subst (λ t → N t) (sym (minus-x0 m)) Nm
minus-N {m} Nm (sN {n} Nn) =
  subst (λ t → N t) (sym (minus-xS m n)) (pred-N (minus-N Nm Nn))

+-N : {m n : D} → N m → N n → N (m + n)
+-N zN Nn = subst (λ t → N t) (sym (+-leftIdentity Nn)) Nn
+-N {n = n} (sN {m} Nm ) Nn =
  subst ((λ t → N t)) (sym (+-Sx m n)) (sN (+-N Nm Nn))

*-N : {m n : D} → N m → N n → N (m * n)
*-N zN Nn = subst (λ t → N t) (sym (*-leftZero Nn)) zN
*-N {n = n} (sN {m} Nm) Nn =
  subst (λ t → N t) (sym (*-Sx m n)) (+-N Nn (*-N Nm Nn))

