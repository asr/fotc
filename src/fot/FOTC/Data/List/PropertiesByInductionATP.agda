------------------------------------------------------------------------------
--  Properties related with lists (using induction on the FOTC lists type)
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.List.PropertiesByInductionATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- Totality properties

-- See Issue https://github.com/asr/apia/issues/81 .
lengthList-NA : D → Set
lengthList-NA ds = N (length ds)
{-# ATP definition lengthList-NA #-}

lengthList-N : ∀ {xs} → List xs → N (length xs)
lengthList-N = List-ind lengthList-NA A[] h
  where
  postulate A[] : lengthList-NA []
  {-# ATP prove A[] #-}

  postulate h : ∀ a {as} → lengthList-NA as → lengthList-NA (a ∷ as)
  {-# ATP prove h #-}

------------------------------------------------------------------------------

-- See Issue https://github.com/asr/apia/issues/81 .
++-assocA : D → D → D → Set
++-assocA ys zs as = (as ++ ys) ++ zs ≡ as ++ ys ++ zs
{-# ATP definition ++-assocA #-}

++-assoc : ∀ {xs} → List xs → ∀ ys zs → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
++-assoc Lxs ys zs = List-ind (++-assocA ys zs) A[] h Lxs
  where
  postulate A[] : ++-assocA ys zs []
  {-# ATP prove A[] #-}

  postulate h : ∀ a {as} → ++-assocA ys zs as → ++-assocA ys zs (a ∷ as)
  {-# ATP prove h #-}
