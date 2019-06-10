------------------------------------------------------------------------------
-- Auxiliary properties of the McCarthy 91 function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.McCarthy91.AuxiliaryProperties where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.Inequalities.Properties using ( x<y→y≤z→x<z )
open import Interactive.FOTC.Data.Nat.Properties
  using ( +-N
        ; ∸-N
        )
open import Interactive.FOTC.Data.Nat.UnaryNumbers
open import Interactive.FOTC.Data.Nat.UnaryNumbers.Inequalities.Properties
  using ( x<x+1 )
open import Interactive.FOTC.Program.McCarthy91.Arithmetic
open import Interactive.FOTC.Program.McCarthy91.McCarthy91

------------------------------------------------------------------------------
--- Auxiliary properties

-- TODO (2019-06-09): Missing proof.
postulate x>100→x<f₉₁-x+11 : ∀ {n} → N n → n > 100' → n < f₉₁ n + 11'

-- Case n ≡ 100 can be proved automatically
-- TODO (2019-06-09): Missing proof.
postulate f₉₁-100 : f₉₁ 100' ≡ 91'

-- TODO (2019-06-09): Missing proof.
postulate  f₉₁x+11<f₉₁x+11 : ∀ n →
                             n ≯ 100' →
                             f₉₁ (n + 11') < f₉₁ (f₉₁ (n + 11')) + 11' →
                             f₉₁ (n + 11') < f₉₁ n + 11'

-- TODO (2019-06-09): Missing proof.
postulate f₉₁-x≯100-helper : ∀ m n →
                             m ≯ 100' →
                             f₉₁ (m + 11') ≡ n →
                             f₉₁ n ≡ 91' →
                             f₉₁ m ≡ 91'

-- TODO (2019-06-09): Missing proofs.
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

-- TODO (2019-06-09): Missing proofs.
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

f₉₁-x≡y : ∀ {m n o} → f₉₁ m ≡ n → o ≡ m → f₉₁ o ≡ n
f₉₁-x≡y h refl = h
