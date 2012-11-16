------------------------------------------------------------------------------
-- Auxiliary properties of the McCarthy 91 function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.McCarthy91.AuxiliaryPropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.Inequalities.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP
open import FOTC.Program.McCarthy91.ArithmeticATP
open import FOTC.Program.McCarthy91.McCarthy91

------------------------------------------------------------------------------
-- Auxiliary equation

postulate mc91-eq-aux : ∀ n → n > [100] → mc91 n ≡ n ∸ [10]
{-# ATP prove mc91-eq-aux #-}

------------------------------------------------------------------------------
--- Auxiliary properties

postulate
  x<mc91x+11>100 : ∀ {n} → N n → n > [100] → n < mc91 n + [11]
{-# ATP prove x<mc91x+11>100 +-N ∸-N x<y→y≤z→x<z x<x+1 x+1≤x∸10+11 #-}


-- Most of them not needed
-- Case n ≡ 100 can be proved automatically
postulate mc91-res-100 : mc91 [100] ≡ [91]
{-# ATP prove mc91-res-100 100+11>100 100+11∸10>100
                           101≡100+11∸10 91≡100+11∸10∸10
#-}

postulate
  mc91x+11<mc91x+11 : ∀ n →
                      n ≯ [100] →
                      mc91 (n + [11]) < mc91 (mc91 (n + [11])) + [11] →
                      mc91 (n + [11]) < mc91 n + [11]
{-# ATP prove mc91x+11<mc91x+11 #-}

postulate
  mc91x-res≯100 : ∀ m n →
                  m ≯ [100] →
                  mc91 (m + [11]) ≡ n → mc91 n ≡ [91] →
                  mc91 m ≡ [91]
{-# ATP prove mc91x-res≯100 #-}

postulate
  mc91-res-110 : mc91 ([99] + [11]) ≡ [100]
  mc91-res-109 : mc91 ([98] + [11]) ≡ [99]
  mc91-res-108 : mc91 ([97] + [11]) ≡ [98]
  mc91-res-107 : mc91 ([96] + [11]) ≡ [97]
  mc91-res-106 : mc91 ([95] + [11]) ≡ [96]
  mc91-res-105 : mc91 ([94] + [11]) ≡ [95]
  mc91-res-104 : mc91 ([93] + [11]) ≡ [94]
  mc91-res-103 : mc91 ([92] + [11]) ≡ [93]
  mc91-res-102 : mc91 ([91] + [11]) ≡ [92]
  mc91-res-101 : mc91 ([90] + [11]) ≡ [91]
{-# ATP prove mc91-res-110 99+11>100 x+11∸10≡Sx #-}
{-# ATP prove mc91-res-109 98+11>100 x+11∸10≡Sx #-}
{-# ATP prove mc91-res-108 97+11>100 x+11∸10≡Sx #-}
{-# ATP prove mc91-res-107 96+11>100 x+11∸10≡Sx #-}
{-# ATP prove mc91-res-106 95+11>100 x+11∸10≡Sx #-}
{-# ATP prove mc91-res-105 94+11>100 x+11∸10≡Sx #-}
{-# ATP prove mc91-res-104 93+11>100 x+11∸10≡Sx #-}
{-# ATP prove mc91-res-103 92+11>100 x+11∸10≡Sx #-}
{-# ATP prove mc91-res-102 91+11>100 x+11∸10≡Sx #-}
{-# ATP prove mc91-res-101 90+11>100 x+11∸10≡Sx #-}

postulate
  mc91-res-99 : mc91 [99] ≡ [91]
  mc91-res-98 : mc91 [98] ≡ [91]
  mc91-res-97 : mc91 [97] ≡ [91]
  mc91-res-96 : mc91 [96] ≡ [91]
  mc91-res-95 : mc91 [95] ≡ [91]
  mc91-res-94 : mc91 [94] ≡ [91]
  mc91-res-93 : mc91 [93] ≡ [91]
  mc91-res-92 : mc91 [92] ≡ [91]
  mc91-res-91 : mc91 [91] ≡ [91]
  mc91-res-90 : mc91 [90] ≡ [91]
{-# ATP prove mc91-res-99 mc91x-res≯100 mc91-res-110 mc91-res-100 #-}
{-# ATP prove mc91-res-98 mc91x-res≯100 mc91-res-109 mc91-res-99 #-}
{-# ATP prove mc91-res-97 mc91x-res≯100 mc91-res-108 mc91-res-98 #-}
{-# ATP prove mc91-res-96 mc91x-res≯100 mc91-res-107 mc91-res-97 #-}
{-# ATP prove mc91-res-95 mc91x-res≯100 mc91-res-106 mc91-res-96 #-}
{-# ATP prove mc91-res-94 mc91x-res≯100 mc91-res-105 mc91-res-95 #-}
{-# ATP prove mc91-res-93 mc91x-res≯100 mc91-res-104 mc91-res-94 #-}
{-# ATP prove mc91-res-92 mc91x-res≯100 mc91-res-103 mc91-res-93 #-}
{-# ATP prove mc91-res-91 mc91x-res≯100 mc91-res-102 mc91-res-92 #-}
{-# ATP prove mc91-res-90 mc91x-res≯100 mc91-res-101 mc91-res-91 #-}

mc91-res-aux : ∀ {m n o} → mc91 m ≡ n → o ≡ m → mc91 o ≡ n
mc91-res-aux h refl = h
