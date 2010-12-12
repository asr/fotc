module Draft.Stream.Postulates where

open import LTC.Base

postulate
  _≈_ : D → D → Set

postulate
  Stream  : D → Set
  consS   : (x : D){xs : D} → (Sxs : Stream xs) → Stream (x ∷ xs)
  headS   : {xs : D} → Stream xs → D
  headS-∷ : (x : D){xs : D}(Sxs : Stream xs) → headS (consS x Sxs) ≡ x
  tailS   : {x xs : D} → Stream (x ∷ xs) → Stream xs
  tailS-∷ : (x : D){xs : D}(Sxs : Stream xs) → {!tailS!} ≈ xs
