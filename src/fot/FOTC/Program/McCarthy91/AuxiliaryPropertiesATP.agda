------------------------------------------------------------------------------
-- Auxiliary properties of the McCarthy 91 function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.McCarthy91.AuxiliaryPropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP using ( x<y→y≤z→x<z )
open import FOTC.Data.Nat.PropertiesATP
  using ( +-N
        ; ∸-N
        )
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.Inequalities.PropertiesATP
  using ( x<x+1 )
open import FOTC.Program.McCarthy91.ArithmeticATP
open import FOTC.Program.McCarthy91.McCarthy91

------------------------------------------------------------------------------
--- Auxiliary properties

postulate x>100→x<f₉₁-x+11 : ∀ {n} → N n → n > 100' → n < f₉₁ n + 11'
{-# ATP prove x>100→x<f₉₁-x+11 +-N ∸-N x<y→y≤z→x<z x<x+1 x+1≤x∸10+11 #-}

-- Case n ≡ 100 can be proved automatically
postulate f₉₁-100 : f₉₁ 100' ≡ 91'
{-# ATP prove f₉₁-100 100+11>100 100+11∸10>100 101≡100+11∸10 91≡100+11∸10∸10 #-}

postulate  f₉₁x+11<f₉₁x+11 : ∀ n →
                             n ≯ 100' →
                             f₉₁ (n + 11') < f₉₁ (f₉₁ (n + 11')) + 11' →
                             f₉₁ (n + 11') < f₉₁ n + 11'
{-# ATP prove f₉₁x+11<f₉₁x+11 #-}

postulate f₉₁-x≯100-helper : ∀ m n →
                             m ≯ 100' →
                             f₉₁ (m + 11') ≡ n →
                             f₉₁ n ≡ 91' →
                             f₉₁ m ≡ 91'
{-# ATP prove f₉₁-x≯100-helper #-}

postulate
  f₉₁-110 : f₉₁ (99' + 11') ≡ 100'
  f₉₁-109 : f₉₁ (98' + 11') ≡ 99'
  f₉₁-108 : f₉₁ (97' + 11') ≡ 98'
  f₉₁-107 : f₉₁ (96' + 11') ≡ 97'
  f₉₁-106 : f₉₁ (95' + 11') ≡ 96'
  f₉₁-105 : f₉₁ (94' + 11') ≡ 95'
  f₉₁-104 : f₉₁ (93' + 11') ≡ 94'
  f₉₁-103 : f₉₁ (92' + 11') ≡ 93'
  f₉₁-102 : f₉₁ (91' + 11') ≡ 92'
  f₉₁-101 : f₉₁ (90' + 11') ≡ 91'
{-# ATP prove f₉₁-110 99+11>100 x+11∸10≡Sx #-}
{-# ATP prove f₉₁-109 98+11>100 x+11∸10≡Sx #-}
{-# ATP prove f₉₁-108 97+11>100 x+11∸10≡Sx #-}
{-# ATP prove f₉₁-107 96+11>100 x+11∸10≡Sx #-}
{-# ATP prove f₉₁-106 95+11>100 x+11∸10≡Sx #-}
{-# ATP prove f₉₁-105 94+11>100 x+11∸10≡Sx #-}
{-# ATP prove f₉₁-104 93+11>100 x+11∸10≡Sx #-}
{-# ATP prove f₉₁-103 92+11>100 x+11∸10≡Sx #-}
{-# ATP prove f₉₁-102 91+11>100 x+11∸10≡Sx #-}
{-# ATP prove f₉₁-101 90+11>100 x+11∸10≡Sx #-}

postulate
  f₉₁-99 : f₉₁ 99' ≡ 91'
  f₉₁-98 : f₉₁ 98' ≡ 91'
  f₉₁-97 : f₉₁ 97' ≡ 91'
  f₉₁-96 : f₉₁ 96' ≡ 91'
  f₉₁-95 : f₉₁ 95' ≡ 91'
  f₉₁-94 : f₉₁ 94' ≡ 91'
  f₉₁-93 : f₉₁ 93' ≡ 91'
  f₉₁-92 : f₉₁ 92' ≡ 91'
  f₉₁-91 : f₉₁ 91' ≡ 91'
  f₉₁-90 : f₉₁ 90' ≡ 91'
{-# ATP prove f₉₁-99 f₉₁-x≯100-helper f₉₁-110 f₉₁-100 #-}
{-# ATP prove f₉₁-98 f₉₁-x≯100-helper f₉₁-109 f₉₁-99 #-}
{-# ATP prove f₉₁-97 f₉₁-x≯100-helper f₉₁-108 f₉₁-98 #-}
{-# ATP prove f₉₁-96 f₉₁-x≯100-helper f₉₁-107 f₉₁-97 #-}
{-# ATP prove f₉₁-95 f₉₁-x≯100-helper f₉₁-106 f₉₁-96 #-}
{-# ATP prove f₉₁-94 f₉₁-x≯100-helper f₉₁-105 f₉₁-95 #-}
{-# ATP prove f₉₁-93 f₉₁-x≯100-helper f₉₁-104 f₉₁-94 #-}
{-# ATP prove f₉₁-92 f₉₁-x≯100-helper f₉₁-103 f₉₁-93 #-}
{-# ATP prove f₉₁-91 f₉₁-x≯100-helper f₉₁-102 f₉₁-92 #-}
{-# ATP prove f₉₁-90 f₉₁-x≯100-helper f₉₁-101 f₉₁-91 #-}

f₉₁-x≡y : ∀ {m n o} → f₉₁ m ≡ n → o ≡ m → f₉₁ o ≡ n
f₉₁-x≡y h refl = h
