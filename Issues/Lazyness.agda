module Issues.Lazyness where

{-
$ agda2atp Issues/Lazyness.agda

yields

An internal error has occurred. Please report this as a bug.
Location of the error: src/FOL/Translation/Internal/Terms.hs:486

but

$ agda2atp -v 20 Issues/Lazyness.agda

yields

An internal error has occurred. Please report this as a bug.
Location of the error: src/AgdaLib/Syntax/DeBruijn.hs:152

The internal error should be the same.
-}

postulate
  D          : Set
  true false : D
  not        : D → D

data _≡_ (x : D) : D → Set where
  refl : x ≡ x

data Bool : D → Set where
  tB : Bool true
  fB : Bool false

foo : ∀ {b0 b1 b2} →
      Bool b1 →
      Bool b2 →
      b0 ≡ not b1 →
      b2 ≡ b2
foo      tB Bb2 b0-eq = refl
foo {b0} fB Bb2 b0-eq = refl
  where
  as : D
  as = b0

  bs : D
  bs = not as
  {-# ATP definition bs #-}

  postulate bar : bs ≡ bs
  {-# ATP prove bar #-}
