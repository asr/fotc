module Draft.FOTC.Data.List.PostulatesVersusDataTypes where

data U : Set where
  _::_ : U → U → U

data ListU : U → Set where
  cons : ∀ x xs → ListU xs → ListU (x :: xs)

tailU : ∀ {x xs} → ListU (x :: xs) → ListU xs
tailU {x} {xs} (cons .x .xs xsL) = xsL

postulate
  D   : Set
  _∷_ : D → D → D

data List : D → Set where
  cons : ∀ x xs → List xs → List (x ∷ xs)

tail : ∀ {x xs} → List (x ∷ xs) → List xs
tail l = {!!}
