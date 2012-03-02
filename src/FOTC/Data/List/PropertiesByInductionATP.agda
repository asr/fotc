------------------------------------------------------------------------------
--  Properties related with lists (using induction on the FOTC list type)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.List.PropertiesByInductionATP where

open import FOTC.Base
open import FOTC.Data.List

------------------------------------------------------------------------------

++-assoc : ∀ {xs ys zs} → List xs → List ys → List zs →
           (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc {xs} {ys} {zs} Lxs Lys Lzs = List-ind A A[] is Lxs
  where
  A : D → Set
  A ds = (ds ++ ys) ++ zs ≡ ds ++ ys ++ zs
  {-# ATP definition A #-}

  postulate A[] : A []
  {-# ATP prove A[] #-}

  postulate is : ∀ d {ds} → A ds → A (d ∷ ds)
  {-# ATP prove is #-}
