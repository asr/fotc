------------------------------------------------------------------------------
-- The booleans properties
------------------------------------------------------------------------------

module LTC.Data.Bool.PropertiesATP where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC.Data.Bool
  using ( _&&_ ; &&-ff ; &&-ft ; &&-tf
        ; Bool ; fB ; tB  -- The LTC booleans type.
        )
open import LTC.Data.Nat.Inequalities using ( _≤_ )
open import LTC.Data.Nat.Inequalities.PropertiesATP using ( S≰0 )
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

&&-proj₁ : {b₁ b₂ : D} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ true → b₁ ≡ true
&&-proj₁ tB _ _    = refl
&&-proj₁ fB tB h = ⊥-elim $ true≠false $ trans (sym h) &&-ft
&&-proj₁ fB fB h = ⊥-elim $ true≠false $ trans (sym h) &&-ff

&&-proj₂ : {b₁ b₂ : D} → Bool b₁ → Bool b₂ → b₁ && b₂ ≡ true → b₂ ≡ true
&&-proj₂ _  tB _   = refl
&&-proj₂ tB fB h = ⊥-elim $ true≠false $ trans (sym h) &&-tf
&&-proj₂ fB fB h = ⊥-elim $ true≠false $ trans (sym h) &&-ff

&&₃-proj₃ : {b₁ b₂ b₃ b₄ : D} →
            Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
            b₁ && b₂ && b₃ && b₄ ≡ true →
            b₃ ≡ true
&&₃-proj₃ _ _ tB _ _ = refl
&&₃-proj₃ _ _ fB _ _ = ⊥-elim prf
  where
    postulate prf : ⊥
    {-# ATP prove prf x&&false≡false false&&x≡false #-}

&&₃-proj₄ : {b₁ b₂ b₃ b₄ : D} →
            Bool b₁ → Bool b₂ → Bool b₃ → Bool b₄ →
            b₁ && b₂ && b₃ && b₄ ≡ true →
            b₄ ≡ true
&&₃-proj₄ _ _ _ tB _ = refl
&&₃-proj₄ _ _ _ fB _ = ⊥-elim prf
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
