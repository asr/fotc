------------------------------------------------------------------------------
-- The division result is correct
------------------------------------------------------------------------------

module PCF.Examples.Division.IsN-ER where

open import LTC.Base

open import Common.Function using ( _$_ )
open import Common.Relation.Binary.PropositionalEquality.PropertiesER
  using ( subst )

open import PCF.Examples.Division.Division using ( div )
open import PCF.Examples.Division.EquationsER  using ( div-x<y ; div-x≥y )
open import PCF.Examples.Division.Specification using ( DIV )

open import PCF.LTC.Data.Nat
  using ( _-_
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import PCF.LTC.Data.Nat.Inequalities using ( GE ; LT )

------------------------------------------------------------------------------
-- The division result is a 'N' when the dividend is less than the divisor.
div-x<y-N : {i j : D} -> LT i j → N (div i j)
div-x<y-N i<j = subst N (sym $ div-x<y i<j) zN

-- The division result is a 'N' when the dividend is greater or equal
-- than the divisor.

--  N (div (i - j) j)       i ≥j → div i j ≡ succ (div (i - j) j)
------------------------------------------------------------------
--                   N (div i j)

div-x≥y-N : {i j : D} → N i → N j →
            (ih : DIV (i - j) j (div (i - j) j)) →
            GE i j →
            N (div i j)
div-x≥y-N Ni Nj ih i≥j = subst N (sym $ div-x≥y Ni Nj i≥j) (sN (∧-proj₁ ih))
