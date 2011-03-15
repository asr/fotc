module Draft.FOTC.Data.Stream.Postulates where

open import FOTC.Base

postulate
  _≈_ : D → D → Set

postulate
  Stream  : D → Set
  consS   : ∀ x {xs} → Stream xs → Stream (x ∷ xs)
  headS   : ∀ {xs} → Stream xs → D
  headS-∷ : ∀ x {xs} → (Sxs : Stream xs) → headS (consS x Sxs) ≈ x
  tailS   : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
  tailS-∷ : ∀ x {xs} → {!!}
