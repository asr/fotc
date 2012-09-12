------------------------------------------------------------------------------
--  Properties related with lists (using induction on the FOTC lists type)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.List.PropertiesByInductionATP where

open import FOTC.Base
open import FOTC.Data.List

------------------------------------------------------------------------------

++-assoc : ∀ {xs} → List xs → ∀ ys zs → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc Lxs ys zs = List-ind A Anil is Lxs
  where
  A : D → Set
  A ds = (ds ++ ys) ++ zs ≡ ds ++ ys ++ zs
  {-# ATP definition A #-}

  postulate Anil : A []
  {-# ATP prove Anil #-}

  postulate is : ∀ d {ds} → A ds → A (d ∷ ds)
  {-# ATP prove is #-}
