------------------------------------------------------------------------------
-- PCF terms properties
------------------------------------------------------------------------------

module LTC.Base.Properties where

open import LTC.Base

open import Common.Function using ( _$_ )

------------------------------------------------------------------------------

postulate
  succInjective : {d e : D} → succ d ≡ succ e → d ≡ e
{-# ATP prove succInjective #-}

postulate
  ∷-injective : {x y xs ys : D} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
{-# ATP prove ∷-injective #-}

≡-list : {x y xs ys : D} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
≡-list refl refl = refl

≡-stream : {x y xs ys : D} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
≡-stream = ≡-list

¬S≡0 : {n : D} → ¬ (succ n ≡ zero)
¬S≡0 S≡0 = 0≠S $ sym S≡0

x≡y→Sx≡Sy : {m n : D} → m ≡ n → succ m ≡ succ n
x≡y→Sx≡Sy refl = refl
