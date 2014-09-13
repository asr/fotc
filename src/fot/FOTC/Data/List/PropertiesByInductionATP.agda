------------------------------------------------------------------------------
--  Properties related with lists (using induction on the FOTC lists type)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.List.PropertiesByInductionATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Totality properties

lengthList-N : ∀ {xs} → List xs → N (length xs)
lengthList-N = List-ind A A[] h
  where
  A : D → Set
  A ds = N (length ds)
  {-# ATP definition A #-}

  postulate A[] : A []
  {-# ATP prove A[] #-}

  postulate h : ∀ a {as} → A as → A (a ∷ as)
  {-# ATP prove h #-}

------------------------------------------------------------------------------

++-assoc : ∀ {xs} → List xs → ∀ ys zs → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc Lxs ys zs = List-ind A A[] h Lxs
  where
  A : D → Set
  A as = (as ++ ys) ++ zs ≡ as ++ ys ++ zs
  {-# ATP definition A #-}

  postulate A[] : A []
  {-# ATP prove A[] #-}

  postulate h : ∀ a {as} → A as → A (a ∷ as)
  {-# ATP prove h #-}
