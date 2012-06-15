{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.List.PostulatesVersusDataTypes where

-- See Agda mailing list.
-- Subject: Agda's unification: postulates versus data types

module M₁ where
  data D : Set where
    _∷_ : D → D → D

  data List : D → Set where
    cons : ∀ x xs → List xs → List (x ∷ xs)

  tail : ∀ {x xs} → List (x ∷ xs) → List xs
  tail {x} {xs} (cons .x .xs xsL) = xsL

module M₂ where
  postulate
    D   : Set
    _∷_ : D → D → D

  data List : D → Set where
    cons : ∀ x xs → List xs → List (x ∷ xs)

  tail : ∀ {x xs} → List (x ∷ xs) → List xs
  tail l = {!!}  -- C-c C-c fails
