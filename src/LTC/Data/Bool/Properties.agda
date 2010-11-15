------------------------------------------------------------------------------
-- The booleans properties
------------------------------------------------------------------------------

module LTC.Data.Bool.Properties where

open import LTC.Base

open import Lib.Function using ( _$_ )

open import LTC.Data.Bool
  using ( _&&_ ; &&-ff ; &&-ft ; &&-tf
        ; Bool ; fB ; tB  -- The LTC booleans type.
        )
open import LTC.Data.Nat.Inequalities using ( _≤_ )
open import LTC.Data.Nat.Inequalities.Properties using ( S≰0 )
open import LTC.Data.Nat.Type
  using ( N ; sN ; zN  -- The LTC natural numbers type.
        )

------------------------------------------------------------------------------
-- Basic properties

&&-Bool : {b₁ b₂ : D} → Bool b₁ → Bool b₂ → Bool (b₁ && b₂)
&&-Bool tB tB = prf
  where
    postulate prf : Bool (true && true)
    {-# ATP prove prf #-}
&&-Bool tB fB = prf
  where
    postulate prf : Bool (true && false)
    {-# ATP prove prf #-}
&&-Bool fB tB = prf
  where
    postulate prf : Bool (false && true)
    {-# ATP prove prf #-}
&&-Bool fB fB = prf
  where
    postulate prf : Bool (false && false)
    {-# ATP prove prf #-}

x&&false≡false : {b : D} → Bool b → b && false ≡ false
x&&false≡false tB = &&-tf
x&&false≡false fB = &&-ff

false&&x≡false : {b : D} → Bool b → false && b ≡ false
false&&x≡false tB = &&-ft
false&&x≡false fB = &&-ff

x&&y≡true→x≡true : {b₁ b₂ : D} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ true →
                   b₁ ≡ true
x&&y≡true→x≡true tB _ _    = refl
x&&y≡true→x≡true fB tB prf = ⊥-elim $ true≠false $ trans (sym prf) &&-ft
x&&y≡true→x≡true fB fB prf = ⊥-elim $ true≠false $ trans (sym prf) &&-ff

x&&y≡true→y≡true : {b₁ b₂ : D} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ true →
                   b₂ ≡ true
x&&y≡true→y≡true _  tB _   = refl
x&&y≡true→y≡true tB fB prf = ⊥-elim $ true≠false $ trans (sym prf) &&-tf
x&&y≡true→y≡true fB fB prf = ⊥-elim $ true≠false $ trans (sym prf) &&-ff

w&&x&&y&&z≡true→y≡true : {b₁ b₂ b₃ b₄ : D} →
                         Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
                         b₁ && b₂ && b₃ && b₄ ≡ true →
                         b₃ ≡ true
w&&x&&y&&z≡true→y≡true Bb₁ Bb₂ tB Bb₄ b₁&&b₂&&b₃&&b₄≡true = refl
w&&x&&y&&z≡true→y≡true {b₁} {b₂} {b₄ = b₄} Bb₁ Bb₂ fB Bb₄ b₁&&b₂&&b₃&&b₄≡true
  =  ⊥-elim prf
  where
    postulate prf : ⊥
    {-# ATP prove prf x&&false≡false false&&x≡false #-}

w&&x&&y&&z≡true→z≡true : {b₁ b₂ b₃ b₄ : D} →
                         Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
                         b₁ && b₂ && b₃ && b₄ ≡ true →
                         b₄ ≡ true
w&&x&&y&&z≡true→z≡true Bb₁ Bb₂ Bb₃ tB b₁&&b₂&&b₃&&b₄≡true = refl
w&&x&&y&&z≡true→z≡true {b₁} {b₂} {b₃} Bb₁ Bb₂ Bb₃ fB
                       b₁&&b₂&&b₃&&b₄≡true = ⊥-elim prf
  where
    postulate prf : ⊥
    {-# ATP prove prf x&&false≡false #-}

------------------------------------------------------------------------------
-- Properties with inequalities

≤-Bool : {m n : D} → N m → N n → Bool (m ≤ n)
≤-Bool {n = n} zN Nn = prf
  where
    postulate prf : Bool (zero ≤ n)
    {-# ATP prove prf #-}
≤-Bool (sN {m} Nm) zN = prf
  where
    postulate prf : Bool (succ m ≤ zero)
    {-# ATP prove prf S≰0 #-}
≤-Bool (sN {m} Nm) (sN {n} Nn) = prf $ ≤-Bool Nm Nn
  where
    postulate prf : Bool (m ≤ n) → Bool (succ m ≤ succ n)
    {-# ATP prove prf #-}
