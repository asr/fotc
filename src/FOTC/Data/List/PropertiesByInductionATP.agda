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
++-assoc {xs} {ys} {zs} Lxs Lys Lzs = List-ind P p[] is Lxs
  where
  P : D → Set
  P ds = (ds ++ ys) ++ zs ≡ ds ++ ys ++ zs
  {-# ATP definition P #-}

  postulate p[] : P []
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove p[] #-}

  postulate is : ∀ d {ds} → P ds → P (d ∷ ds)
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove is #-}
